using System.Text;
using System.Text.Json;
using Microsoft.AspNetCore.Http.HttpResults;
using Microsoft.AspNetCore.Mvc;
using Microsoft.Extensions.Logging;
using Crux.Communications;
using Crux.Communications.Infrastructure;
using Crux.Notifications.Twilio;

namespace Crux.Api.Endpoints;

internal static class CommunicationsWebhookEndpoints
{
    public static IEndpointRouteBuilder MapCommunicationsWebhookEndpoints(this IEndpointRouteBuilder app)
    {
        app.MapPost(CommunicationsRoutes.SendGridMarketingWebhook, SendGridMarketingWebhook)
            .WithName("Comms_SendGridMarketingWebhook")
            .ExcludeFromDescription()
            .AllowAnonymous()
            .Produces(StatusCodes.Status200OK)
            .Produces(StatusCodes.Status400BadRequest)
            .Produces(StatusCodes.Status401Unauthorized);

        app.MapPost(TwilioWebhookRoutes.MessagingStatus, TwilioMessagingWebhook)
            .WithName("Comms_TwilioMessagingWebhook")
            .ExcludeFromDescription()
            .AllowAnonymous()
            .Produces(StatusCodes.Status200OK)
            .Produces(StatusCodes.Status400BadRequest)
            .Produces(StatusCodes.Status401Unauthorized);

        var unsub = app.MapGroup(CommunicationsRoutes.Unsubscribe).AllowAnonymous().ExcludeFromDescription();
        unsub.MapPost("/", PostUnsubscribe).WithName("Comms_OneClickUnsubscribe");
        unsub.MapGet("/", GetUnsubscribe).WithName("Comms_UnsubscribePage");

        return app;
    }

    private static async Task<Results<Ok<DeliveryEventResult>, ProblemHttpResult, UnauthorizedHttpResult>>
        SendGridMarketingWebhook(
            HttpRequest request,
            SendGridWebhookVerifier verifier,
            DeliveryEventProcessor processor,
            IHostEnvironment environment,
            ILoggerFactory loggerFactory,
            CancellationToken ct)
    {
        var logger = loggerFactory.CreateLogger("Comms.SendGridWebhook");

        string rawBody;
        using (var reader = new StreamReader(request.Body, Encoding.UTF8))
            rawBody = await reader.ReadToEndAsync(ct);

        var signature = request.Headers[SendGridWebhookVerifier.SignatureHeader].ToString();
        var timestamp = request.Headers[SendGridWebhookVerifier.TimestampHeader].ToString();

        var verification = verifier.Verify(rawBody, signature, timestamp);
        switch (verification)
        {
            case WebhookVerification.Invalid:
                logger.LogWarning("Rejected SendGrid marketing webhook: signature verification failed.");
                return TypedResults.Unauthorized();
            case WebhookVerification.Skipped when environment.IsProduction():
                logger.LogWarning(
                    "Rejected SendGrid marketing webhook: no Communications:Webhook:SendGridPublicKey is configured.");
                return TypedResults.Unauthorized();
            case WebhookVerification.Skipped:
                logger.LogWarning(
                    "SendGrid marketing webhook signature verification SKIPPED " +
                    "(no Communications:Webhook:SendGridPublicKey configured - dev/mock only).");
                break;
        }

        IReadOnlyList<DeliveryEvent> events;
        try
        {
            events = SendGridEventParser.Parse(rawBody);
        }
        catch (JsonException ex)
        {
            logger.LogWarning("SendGrid marketing webhook had an unparseable body: {Error}", ex.Message);
            return TypedResults.Problem(title: "Bad webhook payload", detail: "Body was not a SendGrid event array.", statusCode: StatusCodes.Status400BadRequest);
        }

        var result = await processor.ProcessAsync(events, ct);
        return TypedResults.Ok(result);
    }

    private static async Task<Results<Ok, ProblemHttpResult, UnauthorizedHttpResult>>
        TwilioMessagingWebhook(
            HttpRequest request,
            TwilioWebhookVerifier verifier,
            TwilioStatusEventProcessor processor,
            IHostEnvironment environment,
            ILoggerFactory loggerFactory,
            CancellationToken ct)
    {
        var logger = loggerFactory.CreateLogger("Comms.TwilioWebhook");

        if (!request.HasFormContentType)
        {
            return TypedResults.Problem(title: "Bad webhook payload", detail: "Twilio Status Callback must be application/x-www-form-urlencoded.", statusCode: StatusCodes.Status400BadRequest);
        }

        var raw = await request.ReadFormAsync(ct);
        var form = raw.ToDictionary(kv => kv.Key, kv => kv.Value.ToString(), StringComparer.Ordinal);

        var url = $"{request.Scheme}://{request.Host}{request.PathBase}{request.Path}{request.QueryString}";

        var signature = request.Headers[TwilioWebhookVerifier.SignatureHeader].ToString();
        var verification = verifier.Verify(url, form, string.IsNullOrEmpty(signature) ? null : signature);
        switch (verification)
        {
            case WebhookVerification.Invalid:
                logger.LogWarning("Rejected Twilio messaging webhook: signature verification failed.");
                return TypedResults.Unauthorized();
            case WebhookVerification.Skipped when environment.IsProduction():
                logger.LogWarning(
                    "Rejected Twilio messaging webhook: no Twilio:AuthToken or TwilioWhatsApp:AuthToken is configured.");
                return TypedResults.Unauthorized();
            case WebhookVerification.Skipped:
                logger.LogWarning(
                    "Twilio messaging webhook signature verification SKIPPED " +
                    "(neither Twilio:AuthToken nor TwilioWhatsApp:AuthToken is configured - dev/mock only).");
                break;
        }

        var outcome = await processor.ProcessAsync(form, ct);
        return outcome == TwilioStatusOutcome.BadRequest
            ? TypedResults.Problem(title: "Bad webhook payload", detail: "Missing MessageSid or MessageStatus.", statusCode: StatusCodes.Status400BadRequest)
            : TypedResults.Ok();
    }

    private const string InvalidLinkBody =
        "This unsubscribe link is missing or invalid. Please use the link from a recent email.";

    private static async Task<Results<Ok<string>, ProblemHttpResult, ContentHttpResult>> PostUnsubscribe(
        HttpRequest request,
        UnsubscribeService unsubscribe,
        [FromQuery] string? token,
        CancellationToken ct)
    {
        var effectiveToken = token;
        var confirmed = false;
        if (request.HasFormContentType)
        {
            var form = await request.ReadFormAsync(ct);
            if (string.IsNullOrWhiteSpace(effectiveToken))
                effectiveToken = form["token"].ToString();
            confirmed = form["confirm"] == "1";
        }

        var outcome = await unsubscribe.UnsubscribeAsync(effectiveToken, ct);
        if (confirmed)
        {
            return outcome == UnsubscribeOutcome.Suppressed
                ? Page(StatusCodes.Status200OK, "Unsubscribed",
                    "You have been unsubscribed and will no longer receive marketing email from us.")
                : Page(StatusCodes.Status400BadRequest, "Invalid link", InvalidLinkBody);
        }

        return outcome == UnsubscribeOutcome.Suppressed
            ? TypedResults.Ok("You have been unsubscribed. You will no longer receive marketing email from us.")
            : TypedResults.Problem(title: "Invalid unsubscribe link", detail: "The unsubscribe token is missing or invalid.", statusCode: StatusCodes.Status400BadRequest);
    }

    private static ContentHttpResult GetUnsubscribe(
        UnsubscribeTokenService tokens,
        [FromQuery] string? token) =>
        tokens.Verify(token) is null
            ? Page(StatusCodes.Status400BadRequest, "Invalid link", InvalidLinkBody)
            : Page(StatusCodes.Status200OK, "Unsubscribe",
                "Select Unsubscribe to stop marketing email from us.",
                "<form method=\"post\"><input type=\"hidden\" name=\"confirm\" value=\"1\"><button type=\"submit\">Unsubscribe</button></form>");

    private static ContentHttpResult Page(int status, string heading, string body, string form = "")
    {
        var html =
            $"""
             <!doctype html>
             <html lang="en"><head><meta charset="utf-8">
             <meta name="viewport" content="width=device-width, initial-scale=1">
             <title>{heading}</title></head>
             <body style="font-family:system-ui,sans-serif;max-width:32rem;margin:4rem auto;padding:0 1rem">
             <h1>{heading}</h1><p>{body}</p>{form}
             </body></html>
             """;
        return TypedResults.Content(html, "text/html", Encoding.UTF8, status);
    }
}
