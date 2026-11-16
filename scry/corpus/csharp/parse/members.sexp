(compilation_unit
  (file_scoped_namespace_declaration
    name: (qualified_name
      qualifier: (identifier Demo)
      name: (identifier Members))
    (class_declaration
      (attribute_list)
      (modifier public)
      (modifier sealed)
      name: (identifier Account)
      type_parameters: (type_parameter_list
        (type_parameter
          name: (identifier T)))
      (base_list
        (identifier Base)
        (generic_name
          (identifier IComparable)
          (type_argument_list
            (generic_name
              (identifier Account)
              (type_argument_list
                (identifier T))))))
      body: (declaration_list
        (field_declaration
          (modifier private)
          (modifier readonly)
          (variable_declaration
            type: (predefined_type int)
            (variable_declarator
              name: (identifier _id)
              value: (integer_literal 0))
            (variable_declarator
              name: (identifier _count))))
        (property_declaration
          (modifier public)
          type: (nullable_type
            type: (predefined_type string))
          name: (identifier Owner)
          accessors: (accessor_list
            (accessor_declaration
              name: (identifier get))
            (accessor_declaration
              name: (identifier set))))
        (property_declaration
          (modifier public)
          type: (predefined_type int)
          name: (identifier Id)
          value: (arrow_expression_clause
            (identifier _id)))
        (property_declaration
          (modifier public)
          type: (generic_name
            (identifier List)
            (type_argument_list
              (generic_name
                (identifier List)
                (type_argument_list
                  (predefined_type int)))))
          name: (identifier Grid)
          accessors: (accessor_list
            (accessor_declaration
              name: (identifier get)))
          value: (object_creation_expression
            type: (generic_name
              (identifier List)
              (type_argument_list
                (generic_name
                  (identifier List)
                  (type_argument_list
                    (predefined_type int)))))
            arguments: (argument_list)))
        (property_declaration
          (modifier public)
          type: (predefined_type decimal)
          name: (identifier Balance)
          accessors: (accessor_list
            (accessor_declaration
              name: (identifier get)
              body: (block
                (return_statement
                  (identifier balance))))
            (accessor_declaration
              (modifier private)
              name: (identifier set)
              body: (block
                (expression_statement
                  (assignment_expression
                    left: (identifier balance)
                    operator: "="
                    right: (identifier value)))))))
        (constructor_declaration
          (modifier public)
          name: (identifier Account)
          parameters: (parameter_list
            (parameter
              type: (predefined_type int)
              name: (identifier id))
            (parameter
              type: (predefined_type string)
              name: (identifier owner)))
          (constructor_initializer
            arguments: (argument_list
              (argument
                expression: (identifier owner))))
          body: (block
            (expression_statement
              (assignment_expression
                left: (identifier _id)
                operator: "="
                right: (identifier id)))))
        (method_declaration
          (modifier public)
          (modifier static)
          type: (nullable_type
            type: (identifier T))
          name: (identifier Find)
          type_parameters: (type_parameter_list
            (type_parameter
              name: (identifier U)))
          parameters: (parameter_list
            (parameter
              type: (generic_name
                (identifier IEnumerable)
                (type_argument_list
                  (identifier U)))
              name: (identifier items))
            (parameter
              type: (generic_name
                (identifier Func)
                (type_argument_list
                  (identifier U)
                  (predefined_type bool)))
              name: (identifier pred)))
          body: (arrow_expression_clause
            (default_expression)))
        (method_declaration
          (modifier public)
          (modifier abstract)
          type: (predefined_type void)
          name: (identifier Close)
          parameters: (parameter_list))))
    (enum_declaration
      (modifier public)
      name: (identifier Color)
      body: (enum_member_declaration_list
        (enum_member_declaration
          name: (identifier Red))
        (enum_member_declaration
          name: (identifier Green)
          value: (integer_literal 2))
        (enum_member_declaration
          name: (identifier Blue))))
    (struct_declaration
      name: (identifier Point)
      body: (declaration_list
        (field_declaration
          (modifier public)
          (variable_declaration
            type: (predefined_type int)
            (variable_declarator
              name: (identifier X))))
        (field_declaration
          (modifier public)
          (variable_declaration
            type: (predefined_type int)
            (variable_declarator
              name: (identifier Y))))))
    (interface_declaration
      name: (identifier IShape)
      body: (declaration_list
        (method_declaration
          type: (predefined_type double)
          name: (identifier Area)
          parameters: (parameter_list))))))
