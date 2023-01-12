# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


import inspect
import json
from jinja2 import Template
import datetime
from global_defines import GlobalDefines
import pprint

class BinaryTemplateGeneratorSpecific:
    def __init__(self, parsing_table, token_length):
        self.__max_size = 1000
        self.__eof_chance = 0.5
        self.__globals = []
        self.__globalIsla=[]
        self.__start_key = None
        self.__parsing_table = parsing_table
        self.__token_length = token_length

    def __generate_header_code(self, name,isla_nonterm_info:json, switch_statement, select_statement, is_start_key, origNameInfo):
        #print("Header Data:", name)


        template = """\
            {%- if is_start_key %}
            struct {{ name }} {
            local string follow[0];
            local int size = 0;
            {%- else %}
            struct {{ name }}(string follow[], int size, int epsilon1) {
            {%- endif %}
            {% filter indent(width=4) %}
            
            //stack anfangs informationen 
            nontermStack+="{{ original_name }}";
            nontermStackIndex=nontermStackIndex+1;
            local int currNontermStackIndex=nontermStackIndex;
            nontermStackId+=currNontermStackIndex;

            //stacklocation
            {{ isla_nonterm_info["stackLocation"] }}

            //struct begin
            {{ isla_nonterm_info["structBegin"] }}

            {{ select }}
            
            {{ switch }} 

            //structEnd
            {{ isla_nonterm_info["structEnd"] }}

            //stack ende
            nontermStack+="({{ original_name }} end)";
            nontermStackId+=currNontermStackIndex;
            nontermStackIndex=nontermStackIndex+1;   
            {%- endfilter %}
            };
        """
        
        tmp = inspect.cleandoc(template)
        j2_template = Template(tmp)
        result = j2_template.render({
            "name": name,
            "original_name":origNameInfo,
            "isla_nonterm_info":isla_nonterm_info,
            "switch": switch_statement,
            "select": select_statement,
            "is_start_key": is_start_key
        })

        # print("Result:")
        # print(result)

        return result

    def __generate_switch_code(self, switch_data, nonterm_spezRules,currNonterm):

        template = """switch (selection) {
            {% for key in switch_data -%}
            case "{{ switch_data[key]["name"] }}":
                {% if key in islaSpezInfo -%}
                nontermStack+="{{ islaSpezInfo[key] }}";
                nontermStackId+=-1;
                nontermStackIndex=nontermStackIndex+1;
                {%- endif %}
                local int epsilon = 1;
                {% for symbol in switch_data[key]["rule"] %}
                    {%- if symbol.token == "" %}
                    {%- elif symbol.label == "terminal" %}
                    char {{ symbol.uid.lower() }}[{{ length }}] = { "{{ symbol.token }}" }; 
                {%- else %}
                
                {% if symbol.include_parent_follow %}
                local int combined_follow_size = size + {{ symbol.follow_size }};
                local string follow_new[combined_follow_size];
                local int i;
                for (i = 0; i < size; i++)
                    follow_new[i] = follow[i];
                {% for follow in symbol.follow %}
                follow_new[{{ loop.index0 }} + size] = "{{follow.token}}";
                {% endfor %} 
                {{ symbol.uid }} {{ symbol.uid.lower() }}(follow_new, combined_follow_size, {% if symbol.follow_contained_epsilon %}1{% else %}0{% endif %}); // {{ symbol.token }}
                {% else %}
                
                    local string follow_new[] = {
                        {% for follow in symbol.follow %}{% if "FOLLOW(" in follow %}/* TODO FOLLOW */{% else %}"{{follow.token}}",{% endif %}{% endfor %} 
                        "NULL"
                    };
                    {{ symbol.uid }} {{ symbol.uid.lower() }}(follow_new, {{ symbol.follow_size }}, {% if symbol.follow_contained_epsilon %}1{% else %}0{% endif %}); // {{ symbol.token }}
                {% endif %}
                {%- endif %}
                epsilon = {% if symbol.follow_contained_epsilon %}1{% else %}0{% endif %};
                {% endfor %}
                break;  
            {% endfor %}
        }
        """
        tmp = inspect.cleandoc(template)
        j2_template = Template(tmp)
        #print("switch_data: ")
        #pprint.pprint(switch_data)


        islaSpezInfo={}
        for first, firstInfo in switch_data.items():
            devRule=""
            #{'A_TERMINAL_370B04':'rule': [{...,'token': '<E>',...},{...,'token': '$',...}]
            for derivationPart in firstInfo["rule"]:
                #adde <E> und § -> am schluss <E>$ -> ganze def rule
                devRule+=derivationPart["token"]
            devRule=f"{{{devRule}}}"
            if devRule in nonterm_spezRules:
                islaSpezInfo[first]=devRule


        result = j2_template.render({
            "switch_data": switch_data,
            "length": self.__token_length,
            "islaSpezInfo": islaSpezInfo
        })

        # print("Result:")
        # print(result)

        return result

    def __generate_select_code(self, isla_nonterm_info, select_data, select_size, is_start_key):
        # print("Select Data:", select_data)

        template = """
            {%- if start %}
                local int epsilon1=0;
            {%- endif %}
            local string possible_val_help[] = { {% for symbol in select -%}{% if symbol["token"] != "" %}"{{ symbol["token"] }}",{% endif %}{% endfor %}};
            local int possible_val_helpIndex = {{ select_index }};

            local char selection[{{ length }}];
  
            //possible val
            local string possible_val[0];
            local int possible_val_Index=-1;
            {{ isla_nonterm_info["possible"] }}

            //pref val
            local int pref_val_Index=-1;
            local string pref_val[0];
            {{ isla_nonterm_info["prefered"] }}
            

            //pref possibility
            {{ isla_nonterm_info["pref_chance"] }}
            if(pref_val_Index==-1){
                pref_possibility=0;
            }

            ReadBytes(selection, FTell(), {{ length }}, pref_val ,possible_val, pref_possibility);
            
            //operation
            {{ isla_nonterm_info["operation"] }}

        """
        tmp = inspect.cleandoc(template)
        j2_template = Template(tmp)


        result = j2_template.render({
            "isla_nonterm_info":isla_nonterm_info,
            "select": select_data,
            "start": is_start_key,
            "select_index": select_size-1,
            "length": self.__token_length
        })

        # print("Result:")
        # print(result)

        return result

    def __generate_code(self, code, ct):

        template = """\
                    // Generation time: {{ time }}

                    

                    //returns index of common list
                    char mergeLists(string list1[],int list1Index, string list2[],int list2Index, string mergedList[]){
                        local int i;
                        for(i=0;i<=list1Index;i++){
                            mergedList+=list1[i];
                        }
                        for(i=0;i<=list2Index;i++){
                            mergedList+=list2[i];
                        }
                        return list1Index + list2Index + 1;
                    }

                    //returns index of common list
                    char addList(string list1[],int list1Index, string mergedList[], int mergedListIndex){
                        local int i;
                        for(i=0;i<=list1Index;i++){
                            mergedList+=list1[i];
                        }
                        return list1Index + mergedListIndex + 1;
                    }

                    //returns Index!
                    char createConjunctionOfLists(string list1[],int list1Index, string mergedList[], int mergedListIndex){
                        local int i;
                        local int j;
                        local int listIndex=-1;
                        for(j=mergedListIndex;j>=0;j--){
                            local byte test=1;
                            for(i=0;i<=list1Index;i++){
                                if(list1[i]==mergedList[j]){
                                    test=0;
                                    listIndex=listIndex+1;
                                    break;
                                }
                            }
                            if(test==1){
                                mergedList-=mergedList[j];
                            }
                        }
                        return listIndex;
                    }


                    {% for entry in globalIsla %}
                    {{entry}}
                    {%- endfor %}
                    {% for entry in globals %}
                    struct {{ entry }}(string follow[], int size){};
                    {%- endfor %}
                    {% for entry in code %}
                    {{ entry }}
                    {% endfor %}
                    SetEvilBit(false);
                    {{ start }} {{ start.lower() }};
                """
        tmp = inspect.cleandoc(template)
        j2_template = Template(tmp)

        result = j2_template.render({
            "globalIsla": self.__globalIsla,
            "globals": self.__globals,
            "start": self.__start_key,
            "code": code,
            "time": ct
        })

        # print("Result:")
        # print(result)

        return result

    def __generate_globals_and_start(self, isla):
        distinct_keys = self.__parsing_table.get_distinct_keys()
        for key in distinct_keys:
            normalized_name = GlobalDefines.normalize(key, "non_terminal")

            #normalize keys in isla
            if(key in isla):
                valueOfCurrentKey=isla.pop(key)
                newKeyValPair = {normalized_name: valueOfCurrentKey}
                isla.update(newKeyValPair)


            if key != "<start>":
                self.__globals.append(normalized_name)
            else:
                self.__start_key = GlobalDefines.normalize(key, "non_terminal")

        #add global isla info to __globalIsla
        if("globalInfo" in isla):
            for item in isla["globalInfo"]:
                self.__globalIsla.append(item)


    def generate_code(self, code, isla, spezRules,originalNameList):
        ct = datetime.datetime.now()
        self.__generate_globals_and_start(isla)


        code_blocks = []
        for key, value in code.get_iterable().items():

            nonterm_spezRules={}
            nonterm_info={}
            currNonterm=value["name"]
            if(currNonterm in isla):
                nonterm_info=isla[currNonterm]
            
            if(currNonterm in spezRules):
                nonterm_spezRules=spezRules[currNonterm]


            select_code = self.__generate_select_code(nonterm_info, value["select"], value["select_size"], currNonterm == self.__start_key)
            switch_code = self.__generate_switch_code(value["switch"], nonterm_spezRules,currNonterm)
            header_code = self.__generate_header_code(currNonterm,nonterm_info, switch_code, select_code, currNonterm == self.__start_key, originalNameList[currNonterm])
            code_blocks.append(header_code)

        return self.__generate_code(code_blocks, ct)
