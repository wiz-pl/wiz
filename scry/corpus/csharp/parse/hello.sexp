(compilation_unit
  (using_directive
    (identifier System))
  (using_directive
    (qualified_name
      qualifier: (qualified_name
        qualifier: (identifier System)
        name: (identifier Collections))
      name: (identifier Generic)))
  (namespace_declaration
    name: (identifier Demo)
    body: (declaration_list
      (class_declaration
        (modifier public)
        (modifier static)
        name: (identifier Program)
        body: (declaration_list
          (method_declaration
            (modifier public)
            (modifier static)
            type: (predefined_type void)
            name: (identifier Main)
            parameters: (parameter_list
              (parameter
                type: (array_type
                  type: (predefined_type string)
                  rank: (array_rank_specifier))
                name: (identifier args)))
            body: (block
              (local_declaration_statement
                (variable_declaration
                  type: (implicit_type var)
                  (variable_declarator
                    name: (identifier name)
                    value: (conditional_expression
                      condition: (binary_expression
                        left: (member_access_expression
                          expression: (identifier args)
                          name: (identifier Length))
                        operator: ">"
                        right: (integer_literal 0))
                      consequence: (element_access_expression
                        expression: (identifier args)
                        subscript: (bracketed_argument_list
                          (argument
                            expression: (integer_literal 0))))
                      alternative: (string_literal "world")))))
              (expression_statement
                (invocation_expression
                  function: (member_access_expression
                    expression: (identifier Console)
                    name: (identifier WriteLine))
                  arguments: (argument_list
                    (argument
                      expression: (interpolated_string_expression
                        (interpolation
                          expression: (identifier name))))))))))))))
