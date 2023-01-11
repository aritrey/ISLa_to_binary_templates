# code in this file adapted from:
# https://github.com/Normynator/BTMeetsCFG/tree/8a0ec99bd6e08dc59c09650631c3cf5afc59817a (private repository)
# last access: 09.01.2023
# GPL-3.0 license 
# Copyright (c) 2022 Norman Ziebal



import argparse
import json
from os import walk, path
from typing import Optional, TextIO
from from_universal_4 import FromUniversal
import py010parser


def print_config(input_file: str, isla_file:str,output_file: str, universal: bool) -> None:
    print(f"Inputfile: {input_file}\nIslafile: {isla_file}\nOutputfile: {output_file}\nTo Universal: {universal}")


def convert_from_universal(input_file: Optional[TextIO],isla_file:Optional[TextIO]) -> str:
    input_grammar = json.load(input_file)
    converter = FromUniversal(input_grammar, isla_file)
    result = converter.convert()
    return result


def convert_to_universal(input_file: Optional[TextIO]) -> str:
    file_as_string = input_file.read()
    py010_parsed = py010parser.parse_string(file_as_string)
    # print(py010_parsed.show())
    for x in range(len(py010_parsed.ext)):
        if isinstance(py010_parsed.ext[x], py010parser.c_ast.Typedef):
            print(py010_parsed.ext[x].show(offset=6))
    return None


def convert_grammar(input_file: Optional[TextIO], isla_file: Optional[TextIO], universal: bool) -> str:
    if not universal:
        return convert_from_universal(input_file,isla_file)
    else:
        return convert_to_universal(input_file)

def create_output_file_path(input_file_path,universal):
    return "output/" + path.splitext(input_file_path)[0].split("/")[-1] + (".json" if universal else ".bt")

def handle_file(input_file_path: str,isla_file_path: str, output_file_path: str = None, universal: bool = None) -> None:
    if universal is None:
        if path.splitext(input_file_path)[1] == ".json":
            universal = False
        else:
            universal = True

    if not output_file_path:
        output_file_path=create_output_file_path(input_file_path,universal)

    print_config(input_file_path,isla_file_path, output_file_path, universal)

    input_file = None
    try:
        input_file = open(input_file_path, 'r')
    except FileNotFoundError:
        print("Input file was not found!")
        exit(1)

    isla_file = None
    try:
        isla_file = open( isla_file_path, 'r')
    except FileNotFoundError:
        print("Isla file was not found!")
        exit(1)

    #print(isla_file)
    result = convert_grammar(input_file,isla_file, universal)

    print(result, file=open(output_file_path, "w"))


def main() -> None:
    parser = argparse.ArgumentParser(description="Converter: From/To Binary Templates")
    parser.add_argument('-i', "--input", dest="input",
                        help="Inputgrammarfile: File")
    parser.add_argument('-l', "--l_isla", dest="l_isla",
                        help="InputIslafile: File")
    parser.add_argument('-o', "--output", dest="output",
                        help="Outputgrammarfile: File")
    parser.add_argument('-u', "--other_files_which_annoy_me_atm", action='store_true',
                        help="Converts to other_files_which_annoy_me_atm, if not set it will convert from other_files_which_annoy_me_atm to binary template.")

    pargs = parser.parse_args()

    if pargs.input:
        print("Single file mode!")
        handle_file(pargs.input,pargs.l_isla, pargs.output, pargs.universal)
    else:
        print("Directory mode!")
        filenames = []
        try:
            _, _, filenames = next(walk("./input"))
        except StopIteration:
            pass

        try:
            _, _, isla = next(walk("./l_isla"))
        except StopIteration:
            pass


        for filename in filenames:
            handle_file("input/" + filename,"l_isla/" + isla[0])


if __name__ == "__main__":
    main()
