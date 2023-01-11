# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal


from universal_first_set import FirstSet
from universal_follow_set import FollowSet
from universal_parsing_table import ParsingTable
from universal_parser_generator import ParserGenerator
from universal_follow_set_specific import FollowSetSpecific
from universal_bt_template_generator import BinaryTemplateGenerator
from universal_bt_template_generator_specific import BinaryTemplateGeneratorSpecific


class UniversalParser:
    def __init__(self, lexer):
        self.__lexer = lexer

    def __generate_first_follow_sets(self):
        tokens = self.__lexer.get_tokens()
        first_set = FirstSet(tokens)
        follow_set = FollowSet(tokens, first_set)


        return first_set, follow_set

    def __generate_parsing_table(self, first_set, follow_set):
        parsing_table = ParsingTable(first_set, follow_set, self.__lexer)

        #print("Parsing Table:", parsing_table)
        #print("Parsing Table:")
        #parsing_table.print()

        return parsing_table

    def __generate_follow_set_specific(self, first_set, follow_set, parsing_table):
        tokens = self.__lexer.get_tokens()
        follow_set_specific = FollowSetSpecific(tokens, first_set, follow_set, parsing_table)

        return follow_set_specific

    def generatePasingTabe(self):
        first_set, follow_set = self.__generate_first_follow_sets()
        parsing_table = self.__generate_parsing_table(first_set, follow_set)
        return parsing_table

    def parse(self, isla=None, spezRules=None,originalNameList=None):
        first_set, follow_set = self.__generate_first_follow_sets()
        parsing_table = self.__generate_parsing_table(first_set, follow_set)
        follow_set_specific = self.__generate_follow_set_specific(first_set, follow_set, parsing_table)
        bt_gen_specific = BinaryTemplateGeneratorSpecific(parsing_table, self.__lexer.get_token_length())
        code = bt_gen_specific.generate_code(follow_set_specific, isla, spezRules,originalNameList)
        # print("Parser Code:\n", code)
        return code
