(compilation_unit
  (class_declaration
    name: (identifier "S")
    body: (declaration_list
      (method_declaration
        type: (predefined_type "int")
        name: (identifier "Run")
        parameters: (parameter_list
          (parameter
            type: (array_type
              type: (predefined_type "int")
              rank: (array_rank_specifier "[]"))
            name: (identifier "xs"))
          (parameter
            type: (predefined_type "string")
            name: (identifier "path")))
        body: (block
          (local_declaration_statement
            (variable_declaration
              type: (predefined_type "int")
              (variable_declarator
                name: (identifier "total")
                value: (integer_literal "0"))))
          (for_statement
            initializer: (variable_declaration
              type: (predefined_type "int")
              (variable_declarator
                name: (identifier "i")
                value: (integer_literal "0")))
            condition: (binary_expression
              left: (identifier "i")
              operator: "<"
              right: (member_access_expression
                expression: (identifier "xs")
                name: (identifier "Length")))
            update: (postfix_unary_expression
              operand: (identifier "i")
              operator: "++")
            body: (block
              (expression_statement
                (assignment_expression
                  left: (identifier "total")
                  operator: "+="
                  right: (element_access_expression
                    expression: (identifier "xs")
                    subscript: (bracketed_argument_list
                      (argument
                        expression: (identifier "i"))))))))
          (foreach_statement
            type: (implicit_type "var")
            left: (identifier "x")
            right: (identifier "xs")
            body: (expression_statement
              (assignment_expression
                left: (identifier "total")
                operator: "-="
                right: (identifier "x"))))
          (while_statement
            condition: (binary_expression
              left: (identifier "total")
              operator: ">"
              right: (integer_literal "100"))
            body: (expression_statement
              (assignment_expression
                left: (identifier "total")
                operator: "/="
                right: (integer_literal "2"))))
          (do_statement
            body: (block
              (expression_statement
                (postfix_unary_expression
                  operand: (identifier "total")
                  operator: "++")))
            condition: (binary_expression
              left: (identifier "total")
              operator: "<"
              right: (integer_literal "10")))
          (if_statement
            condition: (binary_expression
              left: (identifier "total")
              operator: "=="
              right: (integer_literal "3"))
            consequence: (return_statement
              (integer_literal "1"))
            alternative: (if_statement
              condition: (binary_expression
                left: (identifier "total")
                operator: "=="
                right: (integer_literal "4"))
              consequence: (block
                (return_statement
                  (integer_literal "2")))))
          (switch_statement
            value: (identifier "total")
            body: (switch_body
              (switch_section
                (case_switch_label
                  (integer_literal "1")))
              (switch_section
                (case_switch_label
                  (integer_literal "2"))
                (expression_statement
                  (assignment_expression
                    left: (identifier "total")
                    operator: "="
                    right: (integer_literal "0")))
                (break_statement "break;"))
              (switch_section
                (default_switch_label "default")
                (return_statement
                  (prefix_unary_expression
                    operator: "-"
                    operand: (integer_literal "1"))))))
          (try_statement
            body: (block
              (using_statement
                (variable_declaration
                  type: (implicit_type "var")
                  (variable_declarator
                    name: (identifier "r")
                    value: (object_creation_expression
                      type: (identifier "StreamReader")
                      arguments: (argument_list
                        (argument
                          expression: (identifier "path"))))))
                body: (block
                  (expression_statement
                    (assignment_expression
                      left: (identifier "total")
                      operator: "="
                      right: (invocation_expression
                        function: (member_access_expression
                          expression: (identifier "r")
                          name: (identifier "Read"))
                        arguments: (argument_list "()")))))))
            (catch_clause
              (catch_declaration
                type: (identifier "IOException")
                name: (identifier "e"))
              (catch_filter_clause
                (binary_expression
                  left: (member_access_expression
                    expression: (identifier "e")
                    name: (identifier "HResult"))
                  operator: "!="
                  right: (integer_literal "0")))
              body: (block
                (throw_statement "throw;")))
            (catch_clause
              body: (block
                (throw_statement
                  (object_creation_expression
                    type: (identifier "InvalidOperationException")
                    arguments: (argument_list
                      (argument
                        expression: (string_literal
                          (string_literal_content "bad"))))))))
            (finally_clause
              (block
                (expression_statement
                  (assignment_expression
                    left: (identifier "total")
                    operator: "="
                    right: (prefix_unary_expression
                      operator: "-"
                      operand: (identifier "total")))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "w")
                value: (invocation_expression
                  function: (member_access_expression
                    expression: (identifier "File")
                    name: (identifier "OpenWrite"))
                  arguments: (argument_list
                    (argument
                      expression: (identifier "path")))))))
          (empty_statement ";")
          (return_statement
            (identifier "total")))))))
