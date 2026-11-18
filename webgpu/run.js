// One WebGPU run of a generated kernel, shared by the browser page and `check.mjs`
// (Deno). Both provide `navigator.gpu`; nothing here is browser- or Node-specific.
//
// A generated module binds every `Array U32` parameter, in order, as a read-only
// storage buffer at @group(0) @binding(0…n-1), and the result at binding n.  All the
// buffers have the same length, as the Wiz kernel's Array.getD with its zero default
// assumes (and as the entry point's `i < arrayLength(&out)` guard enforces).

export async function runWebGPU({ shader, a, b, label = 'kernel', workgroupSize = 64 }) {
  if (!navigator.gpu) {
    return { ok: false, stage: 'device', error: 'navigator.gpu is not available (this browser has WebGPU off or the page is not a secure context)' };
  }
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) return { ok: false, stage: 'device', error: 'no WebGPU adapter (a GPU or a software Vulkan/ANGLE driver is needed)' };
  const device = await adapter.requestDevice();
  const info = adapter.info || {};
  const n = a.length;
  if (b.length !== n) return { ok: false, stage: 'host', error: `buffer lengths differ: a=${n}, b=${b.length}` };

  const messages = [];
  device.pushErrorScope('validation');
  const module = device.createShaderModule({ code: shader, label });
  // `getCompilationInfo` is where naga's validation diagnostics appear.  A WGSL error is
  // a result, not an exception, so report the messages instead of failing the run.
  if (module.getCompilationInfo) {
    const ci = await module.getCompilationInfo();
    for (const m of ci.messages) messages.push({ type: m.type, line: m.lineNum, column: m.linePos, message: m.message });
  }
  const shaderErrors = messages.filter((m) => m.type === 'error');
  if (shaderErrors.length) {
    await device.popErrorScope();
    return { ok: false, stage: 'shader', info, messages };
  }

  const usage = GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST | GPUBufferUsage.COPY_SRC;
  const mk = (values) => {
    const buf = device.createBuffer({ size: Math.max(4, values.length * 4), usage });
    device.queue.writeBuffer(buf, 0, new Uint32Array(values));
    return buf;
  };
  const aBuf = mk(a);
  const bBuf = mk(b);
  const outBuf = mk(new Array(n).fill(0));
  const staging = device.createBuffer({ size: Math.max(4, n * 4), usage: GPUBufferUsage.MAP_READ | GPUBufferUsage.COPY_DST });

  const pipeline = device.createComputePipeline({ layout: 'auto', compute: { module, entryPoint: 'main' } });
  const group = device.createBindGroup({
    layout: pipeline.getBindGroupLayout(0),
    entries: [
      { binding: 0, resource: { buffer: aBuf } },
      { binding: 1, resource: { buffer: bBuf } },
      { binding: 2, resource: { buffer: outBuf } },
    ],
  });
  const encoder = device.createCommandEncoder();
  const pass = encoder.beginComputePass();
  pass.setPipeline(pipeline);
  pass.setBindGroup(0, group);
  pass.dispatchWorkgroups(Math.ceil(n / workgroupSize));
  pass.end();
  encoder.copyBufferToBuffer(outBuf, 0, staging, 0, Math.max(4, n * 4));
  device.queue.submit([encoder.finish()]);

  const validation = await device.popErrorScope();
  if (validation) return { ok: false, stage: 'validation', info, messages, error: validation.message };

  await staging.mapAsync(GPUMapMode.READ);
  const out = Array.from(new Uint32Array(staging.getMappedRange()).slice(0, n));
  staging.unmap();
  device.destroy();
  return { ok: true, info, messages, out };
}

export function compare(out, expected) {
  if (out.length !== expected.length) return false;
  return out.every((v, i) => v === expected[i]);
}
