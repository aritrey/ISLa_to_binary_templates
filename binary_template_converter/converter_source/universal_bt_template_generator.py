# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


import inspect
from jinja2 import Template


class BinaryTemplateGenerator:
    def __init__(self, length):
        self.__max_size = 1000
        self.__eof_chance = 0.5
        self.__length = length

    def generate_code(self, globals_, evilbit, start_key, structs, nullables):
        template = """\
            /* THIS FILE IS AUTOGENERATED. DO NOT CHANGE. */
            
            {% for global in globals -%}
            struct {{ global }};
            {% endfor %}
            
            // Nullables:
            {% for nullable in nullables -%}
            // {{ nullable }}
            {% endfor %}
            
            local int top = 0;
            local string stack[{{ max_size }}];
            
            {% for struct in structs %}
            struct {{ struct.uid }} { // {{ struct.key }} nullable: {{ struct.nullable }}
                if (top == 0 && FEof({% if struct.eof_rule %}{{eof_chance}}{% else %}0.0{% endif %})) {
                    {% for token in struct.eof_rule.rule -%}
                    {%- if token.label == "terminal" -%}
                    {%- if token.token == "" -%}
                        // Nothing to do, epsilon in rule
                    {%- else -%}
                    char {{ token.uid.lower() }}; // {{ token.token }}
                    {%- endif %}
                    {%- else -%}
                    {{ token.uid }} {{ token.uid.lower() }}; // {{ token.token }}
                    {%- endif %}
                    {% endfor %}
                } else {
                    local char val[{{ length }}];
                    if (top != 0) {
                        local string pref_val[] = { {% for pref in struct.pref_values_1 -%}{{ pref }},{% endfor %}};
                        ReadBytes(val, FTell(), {{ length }}, pref_val);
                    } else {
                        local string pref_val[] = { {% for pref in struct.pref_values_0 -%}{{ pref }},{% endfor %}};
                        ReadBytes(val, FTell(), {{ length }}, pref_val);
                    }
                    switch (val) {
                        {% for entry in struct.rule_mapping -%}
                        {%- if entry.symbol == '$' -%}
                        {%- else -%}
                        case "{{ entry.symbol }}":
                            {% for token in entry.rule -%}
                            {%- if token.label == "terminal" -%}
                            {%- if token.token == "" -%}
                            {%- else -%}
                            char {{ token.uid.lower() }}[{{ length }}] = { "{{ token.token }}" }; // {{ token.token }}
                            {%- endif %}
                            {%- else -%}
                            {% if token.label == "instruction" -%}
                            {{ token.uid }}; // {{ token.token }}
                            local int i;
                            {% else %}
                            {{ token.uid }} {{ token.uid.lower() }}; // {{ token.token }}
                            {% endif %}
                            {%- endif %}
                            {% endfor %}
                            break;
                        {%- endif %}
                        {% endfor %}
                    };
                }
            };
            {% endfor %}
            
            {% if evilbit -%}
            SetEvilBit(true);
            {%- else -%}
            SetEvilBit(false);
            {%- endif %}
            {{ start_key }} start;
        """

        data = {
            "max_size": self.__max_size,
            "evilbit": evilbit,
            "globals": globals_,
            "start_key": start_key,
            "structs": structs,
            "nullables": nullables,
            "eof_chance": self.__eof_chance,
            "length": self.__length
        }

        tmp = inspect.cleandoc(template)
        j2_template = Template(tmp)
        return j2_template.render(data)
