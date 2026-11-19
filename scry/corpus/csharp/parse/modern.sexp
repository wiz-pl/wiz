(compilation_unit
  (using_directive
    (identifier "System"))
  (using_directive
    (qualified_name
      qualifier: (identifier "System")
      name: (identifier "Math")))
  (file_scoped_namespace_declaration
    name: (qualified_name
      qualifier: (identifier "Demo")
      name: (identifier "Modern")))
  (record_declaration
    (modifier "public")
    name: (identifier "Point")
    (parameter_list
      (parameter
        type: (predefined_type "int")
        name: (identifier "X"))
      (parameter
        type: (predefined_type "int")
        name: (identifier "Y"))))
  (class_declaration
    (modifier "public")
    name: (identifier "Shapes")
    body: (declaration_list
      (method_declaration
        (modifier "public")
        type: (predefined_type "string")
        name: (identifier "Label")
        parameters: (parameter_list
          (parameter
            type: (predefined_type "int")
            name: (identifier "n")))
        body: (arrow_expression_clause
          (switch_expression
            (identifier "n")
            (switch_expression_arm
              (constant_pattern
                (integer_literal "0"))
              (string_literal
                (string_literal_content "zero")))
            (switch_expression_arm
              (discard "_")
              (interpolated_string_expression
                (interpolation_start "$")
                (string_content "n=")
                (interpolation
                  (interpolation_brace "{")
                  expression: (identifier "n")
                  (interpolation_brace "}")))))))
      (method_declaration
        (modifier "public")
        type: (identifier "Point")
        name: (identifier "Move")
        parameters: (parameter_list
          (parameter
            type: (identifier "Point")
            name: (identifier "p")))
        body: (arrow_expression_clause
          (with_expression
            (identifier "p")
            (with_initializer
              (identifier "X")
              (binary_expression
                left: (member_access_expression
                  expression: (identifier "p")
                  name: (identifier "X"))
                operator: "+"
                right: (integer_literal "1"))))))
      (method_declaration
        (modifier "public")
        type: (array_type
          type: (predefined_type "int")
          rank: (array_rank_specifier "[]"))
        name: (identifier "Sizes")
        parameters: (parameter_list "()")
        body: (arrow_expression_clause
          (collection_expression
            (collection_element
              (expression_element
                (integer_literal "1")))
            (collection_element
              (expression_element
                (integer_literal "2")))
            (collection_element
              (expression_element
                (integer_literal "3"))))))
      (method_declaration
        (modifier "public")
        type: (predefined_type "string")
        name: (identifier "Join")
        parameters: (parameter_list
          (parameter
            type: (array_type
              type: (predefined_type "string")
              rank: (array_rank_specifier "[]"))
            name: (identifier "parts")))
        body: (arrow_expression_clause
          (invocation_expression
            function: (member_access_expression
              expression: (predefined_type "string")
              name: (identifier "Join"))
            arguments: (argument_list
              (argument
                expression: (character_literal
                  (character_literal_content ",")))
              (argument
                expression: (query_expression
                  (from_clause
                    name: (identifier "p")
                    (identifier "parts"))
                  (where_clause
                    (binary_expression
                      left: (member_access_expression
                        expression: (identifier "p")
                        name: (identifier "Length"))
                      operator: ">"
                      right: (integer_literal "0")))
                  (select_clause
                    (invocation_expression
                      function: (member_access_expression
                        expression: (identifier "p")
                        name: (identifier "Trim"))
                      arguments: (argument_list "()"))))))))))))
