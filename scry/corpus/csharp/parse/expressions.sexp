(compilation_unit
  (class_declaration
    name: (identifier "E")
    body: (declaration_list
      (method_declaration
        type: (predefined_type "object")
        name: (identifier "M")
        parameters: (parameter_list
          (parameter
            type: (predefined_type "object")
            name: (identifier "o"))
          (parameter
            type: (predefined_type "int")
            name: (identifier "a"))
          (parameter
            type: (predefined_type "int")
            name: (identifier "b")))
        body: (block
          (local_declaration_statement
            (variable_declaration
              type: (predefined_type "int")
              (variable_declarator
                name: (identifier "c")
                value: (binary_expression
                  left: (binary_expression
                    left: (binary_expression
                      left: (binary_expression
                        left: (identifier "a")
                        operator: "+"
                        right: (binary_expression
                          left: (identifier "b")
                          operator: "*"
                          right: (integer_literal "2")))
                      operator: "-"
                      right: (binary_expression
                        left: (parenthesized_expression
                          (binary_expression
                            left: (identifier "a")
                            operator: "-"
                            right: (identifier "b")))
                        operator: "%"
                        right: (integer_literal "3")))
                    operator: "<<"
                    right: (integer_literal "1"))
                  operator: ">>"
                  right: (integer_literal "2")))))
          (local_declaration_statement
            (variable_declaration
              type: (predefined_type "bool")
              (variable_declarator
                name: (identifier "d")
                value: (binary_expression
                  left: (binary_expression
                    left: (binary_expression
                      left: (identifier "a")
                      operator: "<"
                      right: (identifier "b"))
                    operator: "&&"
                    right: (binary_expression
                      left: (identifier "b")
                      operator: "<="
                      right: (identifier "c")))
                  operator: "||"
                  right: (binary_expression
                    left: (prefix_unary_expression
                      operator: "!"
                      operand: (parenthesized_expression
                        (binary_expression
                          left: (identifier "a")
                          operator: "=="
                          right: (identifier "c"))))
                    operator: "^"
                    right: (boolean_literal "true"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "s")
                value: (binary_expression
                  left: (as_expression
                    expression: (identifier "o")
                    operator: "as"
                    type: (predefined_type "string"))
                  operator: "??"
                  right: (string_literal
                    (string_literal_content "none"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "n")
                value: (binary_expression
                  left: (cast_expression
                    type: (predefined_type "int")
                    value: (identifier "o"))
                  operator: "+"
                  right: (cast_expression
                    type: (predefined_type "long")
                    value: (identifier "a"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "t")
                value: (cast_expression
                  type: (identifier "a")
                  value: (prefix_unary_expression
                    operator: "-"
                    operand: (identifier "b"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "u")
                value: (conditional_expression
                  condition: (is_pattern_expression
                    expression: (identifier "o")
                    pattern: (declaration_pattern
                      type: (predefined_type "string")
                      name: (identifier "str")))
                  consequence: (member_access_expression
                    expression: (identifier "str")
                    name: (identifier "Length"))
                  alternative: (prefix_unary_expression
                    operator: "-"
                    operand: (integer_literal "1"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "v")
                value: (is_pattern_expression
                  expression: (identifier "o")
                  pattern: (negated_pattern
                    (constant_pattern
                      (null_literal "null")))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "arr")
                value: (array_creation_expression
                  type: (array_type
                    type: (predefined_type "int")
                    rank: (array_rank_specifier
                      (identifier "a")))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "arr2")
                value: (implicit_array_creation_expression
                  initializer: (initializer_expression
                    (integer_literal "1")
                    (integer_literal "2")
                    (integer_literal "3"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "arr3")
                value: (array_creation_expression
                  type: (array_type
                    type: (predefined_type "string")
                    rank: (array_rank_specifier "[]"))
                  initializer: (initializer_expression
                    (string_literal
                      (string_literal_content "x"))
                    (verbatim_string_literal "@\"c:\\dir\"")
                    (invocation_expression
                      function: (member_access_expression
                        expression: (character_literal
                          (character_literal_content "q"))
                        name: (identifier "ToString"))
                      arguments: (argument_list "()")))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "list")
                value: (object_creation_expression
                  type: (generic_name
                    (identifier "List")
                    (type_argument_list
                      (predefined_type "string")))
                  initializer: (initializer_expression
                    (string_literal
                      (string_literal_content "a"))
                    (string_literal
                      (string_literal_content "b")))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "p")
                value: (object_creation_expression
                  type: (identifier "Point")
                  initializer: (initializer_expression
                    (assignment_expression
                      left: (identifier "X")
                      operator: "="
                      right: (integer_literal "1"))
                    (assignment_expression
                      left: (identifier "Y")
                      operator: "="
                      right: (integer_literal "2")))))))
          (local_declaration_statement
            (variable_declaration
              type: (generic_name
                (identifier "Func")
                (type_argument_list
                  (predefined_type "int")
                  (predefined_type "int")))
              (variable_declarator
                name: (identifier "f")
                value: (lambda_expression
                  parameters: (implicit_parameter "x")
                  body: (binary_expression
                    left: (identifier "x")
                    operator: "*"
                    right: (integer_literal "2"))))))
          (local_declaration_statement
            (variable_declaration
              type: (generic_name
                (identifier "Func")
                (type_argument_list
                  (predefined_type "int")
                  (predefined_type "int")
                  (predefined_type "int")))
              (variable_declarator
                name: (identifier "g")
                value: (lambda_expression
                  parameters: (parameter_list
                    (parameter
                      name: (identifier "x"))
                    (parameter
                      name: (identifier "y")))
                  body: (block
                    (return_statement
                      (binary_expression
                        left: (identifier "x")
                        operator: "+"
                        right: (identifier "y"))))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "r")
                value: (invocation_expression
                  function: (member_access_expression
                    expression: (invocation_expression
                      function: (member_access_expression
                        expression: (identifier "Enumerable")
                        name: (generic_name
                          (identifier "Empty")
                          (type_argument_list
                            (predefined_type "int"))))
                      arguments: (argument_list "()"))
                    name: (identifier "Count"))
                  arguments: (argument_list "()")))))
          (expression_statement
            (assignment_expression
              left: (identifier "c")
              operator: "+="
              right: (binary_expression
                left: (conditional_access_expression
                  expression: (element_access_expression
                    expression: (invocation_expression
                      function: (identifier "f")
                      arguments: (argument_list
                        (argument
                          expression: (identifier "a"))))
                    subscript: (bracketed_argument_list
                      (argument
                        expression: (integer_literal "0"))))
                  name: (identifier "Length"))
                operator: "??"
                right: (integer_literal "0"))))
          (expression_statement
            (assignment_expression
              left: (identifier "c")
              operator: ">>="
              right: (integer_literal "1")))
          (expression_statement
            (assignment_expression
              left: (identifier "a")
              operator: "="
              right: (assignment_expression
                left: (identifier "b")
                operator: "="
                right: (identifier "c"))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "q")
                value: (typeof_expression
                  type: (predefined_type "string")))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "z")
                value: (default_expression
                  type: (predefined_type "int")))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "w")
                value: (member_access_expression
                  expression: (postfix_unary_expression
                    operand: (identifier "s")
                    operator: "!")
                  name: (identifier "Length")))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "i")
                value: (interpolated_string_expression
                  (interpolation_start "$")
                  (interpolation
                    (interpolation_brace "{")
                    expression: (identifier "a")
                    (interpolation_alignment_clause
                      (integer_literal "5"))
                    (interpolation_brace "}"))
                  (string_content " and ")
                  (interpolation
                    (interpolation_brace "{")
                    expression: (identifier "b")
                    (interpolation_format_clause ":N2")
                    (interpolation_brace "}"))
                  (string_content " and ")
                  (string_content "{{literal}} ")
                  (interpolation
                    (interpolation_brace "{")
                    expression: (invocation_expression
                      function: (member_access_expression
                        expression: (identifier "s")
                        name: (identifier "Substring"))
                      arguments: (argument_list
                        (argument
                          expression: (integer_literal "0"))
                        (argument
                          expression: (integer_literal "1"))))
                    (interpolation_brace "}"))))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "vi")
                value: (interpolated_string_expression
                  (interpolation_start "$@")
                  (string_content "C:\\")
                  (interpolation
                    (interpolation_brace "{")
                    expression: (identifier "s")
                    (interpolation_brace "}"))
                  (string_content "\\x")))))
          (expression_statement
            (invocation_expression
              function: (identifier "Helper")
              arguments: (argument_list
                (argument
                  (modifier "ref")
                  expression: (identifier "a"))
                (argument
                  (modifier "out")
                  expression: (declaration_expression
                    type: (implicit_type "var")
                    name: (identifier "k")))
                (argument
                  (modifier "out")
                  expression: (declaration_expression
                    type: (predefined_type "int")
                    name: (identifier "k2")))
                (argument
                  name: (identifier "name")
                  expression: (string_literal
                    (string_literal_content "x"))))))
          (return_statement
            (binary_expression
              left: (postfix_unary_expression
                operand: (identifier "a")
                operator: "++")
              operator: "+"
              right: (prefix_unary_expression
                operator: "--"
                operand: (identifier "b")))))))))
