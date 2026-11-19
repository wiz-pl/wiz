(compilation_unit
  (file_scoped_namespace_declaration
    name: (identifier "Corpus"))
  (record_declaration
    (modifier "public")
    name: (identifier "Amount")
    (parameter_list
      (parameter
        type: (predefined_type "int")
        name: (identifier "Minor"))))
  (class_declaration
    (modifier "public")
    (modifier "partial")
    name: (identifier "Contextual")
    body: (declaration_list
      (property_declaration
        (modifier "public")
        (modifier "required")
        type: (predefined_type "int")
        name: (identifier "Scale")
        accessors: (accessor_list
          (accessor_declaration
            name: "get")
          (accessor_declaration
            name: "set")))
      (method_declaration
        (modifier "public")
        type: (identifier "Amount")
        name: (identifier "Convert")
        parameters: (parameter_list
          (parameter
            type: (identifier "Amount")
            name: (identifier "amount")))
        body: (arrow_expression_clause
          (with_expression
            (identifier "amount")
            (with_initializer
              (identifier "Minor")
              (binary_expression
                left: (member_access_expression
                  expression: (identifier "amount")
                  name: (identifier "Minor"))
                operator: "*"
                right: (identifier "Scale"))))))
      (method_declaration
        (modifier "public")
        (modifier "static")
        type: (predefined_type "int")
        name: (identifier "Count")
        parameters: (parameter_list
          (parameter
            type: (array_type
              type: (predefined_type "int")
              rank: (array_rank_specifier "[]"))
            name: (identifier "items")))
        body: (block
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "with")
                value: (member_access_expression
                  expression: (identifier "items")
                  name: (identifier "Length")))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "partial")
                value: (identifier "with"))))
          (local_declaration_statement
            (variable_declaration
              type: (implicit_type "var")
              (variable_declarator
                name: (identifier "required")
                value: (identifier "partial"))))
          (return_statement
            (identifier "required"))))
      (method_declaration
        (modifier "public")
        (modifier "static")
        type: (predefined_type "string")
        name: (identifier "Middle")
        parameters: (parameter_list
          (parameter
            type: (predefined_type "string")
            name: (identifier "text")))
        body: (arrow_expression_clause
          (conditional_expression
            condition: (is_pattern_expression
              expression: (identifier "text")
              pattern: (list_pattern
                (constant_pattern
                  (character_literal
                    (character_literal_content "[")))
                (slice_pattern
                  (declaration_pattern
                    type: (implicit_type "var")
                    name: (identifier "middle")))
                (constant_pattern
                  (character_literal
                    (character_literal_content "]")))))
            consequence: (identifier "middle")
            alternative: (identifier "text")))))))
