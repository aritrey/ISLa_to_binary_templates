
from datetime import datetime
from enum import Enum
import json
import os
import os.path
import time
from isla.derivation_tree import DerivationTree
from isla.evaluator import evaluate
from isla.parser import EarleyParser
from isla.solver import ISLaSolver, CostSettings, GrammarBasedBlackboxCostComputer, CostWeightVector
from isla.language import parse_isla
from grammar_graph.gg import GrammarGraph
import matplotlib.pyplot as plt
import subprocess
import re
import sys
from grammar_graph import gg

#from tabulate import tabulate


class TimeOutException(Exception):
    def __init__(self, message):
        super(TimeOutException, self).__init__(message)

class GeneratedBy(Enum):
    ISLA = "isla"
    ISLA_WRONG = "isla_wrong"
    FORMAT_FUZZER = "formatFuzzer"
    PARENT_TOOL="parent_tool"
class Testtypes(Enum):
    COLLECT_RESULTS="collect_results"
    GENERATE_FILES = "generate_files_test"
    PARSE_WITH_ISLA = "parse_with_isla"
    PARSE_WITH_FORMAT_FUZZER = "parse_with_formatFuzzer"
    KPATH_COVERAGE="k_paths_test"

class Tests():
    def __init__(self,testInfo,GRAMMAR, langageName, testToken):
        self.testDir=f"test_output/{testToken}/{langageName}"
        self.testInfo=testInfo
        self.GRAMMAR=GRAMMAR
        self.generate_files_time=60#time in seconds
        self.number_of_iteration=3
        self.langageName=langageName
        sys.setrecursionlimit(3000)

    def addContent(self, test, content):
        true_count=0
        ges_count=0
        wrong_count=0

        with open(test, 'r') as f:
            data = f.read()
            groups=re.findall("_____RESULTS:\nAmmount parsed: ([0-9]+)\nAmmount parsed right: ([0-9]+)\nAmmount parsed wrong: ([0-9]+)",data)
            for group in groups:
                ges_count+=int(group[0])
                true_count+=int(group[1])
                wrong_count+=int(group[2])

        testCount=len(groups)
        if(testCount!=self.number_of_iteration):
            print("possibly wrong values found")
        content.append(str(int(round(ges_count/testCount,0))))
        content.append(str(int(round(true_count/testCount,0))))
        content.append(str(int(round(wrong_count/testCount,0))))


    #generates latex tikzpicture from k-path data (k-path acumulated)
    def get_latex_tikzpicture_from_kpath(self):   # get k-pah coverage 
        print("begin grap k-path")
        for i in range(self.number_of_iteration):
            for generator_used in [GeneratedBy.ISLA,GeneratedBy.FORMAT_FUZZER]:
                f=open(self.__get_test_result_name(generator_used, None,Testtypes.KPATH_COVERAGE.value, iteration=i),"w")
                if(generator_used==GeneratedBy.FORMAT_FUZZER):
                    print("""\\begin{figure}
\\centering
    \\begin{tikzpicture}%[scale=1.5]

    \\begin{axis}[
      height=7cm,
      width=15cm,
      xtickmin=0,
xtickmax=1000,
    xmajorgrids        = true,
      ylabel={generated files},
      ylabel={coverage in percent},
      yticklabels = {0,0,20,40,60,80,100},
    legend style={at={(0.55,0.6)},anchor=north west},
    ]""",file=f)
                else:
                    print("""\\begin{figure}

            \\begin{tikzpicture}
            \\begin{axis}[
            ylabel={generated output files},
            ylabel={files in percent},

        """,file=f) 
                colors=["blue","cyan","gray","green","red"]
                for test_i,info in enumerate(self.testInfo):  
                        filename=info["testname"]
                        read_from_file=self.__get_test_result_name(generator_used, filename, Testtypes.KPATH_COVERAGE.value, iteration=i)
                        str = open(read_from_file, 'r').read()
                        str=str.split("[")[1]
                        str=str.split("]")[0]
                        str_list=str.split(',')
                        float_list=[float(x) for x in str_list]

                        print(f"%{filename}\n\\addplot  [mark=none, color={colors[test_i%len(colors)]}] coordinates {{",file=f)
                        coverage1Seen=False
                        for idx, coverage in enumerate(float_list):
                            if(idx==1000 and generator_used==GeneratedBy.FORMAT_FUZZER):
                                break
                            if(coverage==1.0 and coverage1Seen==False):
                                print(idx+1)
                                coverage1Seen=True
                            print(f"({idx+1},{coverage})",file=f)
                        
                        print(f"({len(float_list)},{float_list[-1]})")
                            
                        adjustedFileName=filename.replace("_", "-" )
                        print(f"}};\\addlegendentry{{{adjustedFileName}}}",file=f)


                caption= generator_used.value.replace("_","-")+" "+self.langageName.replace("_","-")
                print(f"""
            \\end{{axis}}
            \\end{{tikzpicture}}

            \\caption{{{caption}}}
            \\label{{{"fig:"+generator_used.value+"_"+self.langageName}}}
        \\end{{figure}}""",file=f)
                f.close()



    #returns result as arithmetic middle of all tests
    def collect_results(self):
        print("collect results beginnt")
        headers=["ergebnisse test", "withISLaParseFormat ges", "withISLaParseFormat R", "withISLaParseFormat W","withFormatParseIsla ges","withFormatParseIsla R","withFormatParseIsla W","withFormatParseFormat ges","withFormatParseFormat R","withFormatParseFormat W","withFormatParseIslaWrong ges","withFormatParseIslaWrong r","withFormatParseIslaWrong w"]
        headers=["ergebnisse test", "w\I P\F ges", "w\I P\F R", "w\I P\F W","w\F P\I ges","w\F P\I R","w\F P\I W","w\F P\F ges","w\F P\F R","w\F P\F W","w\F P\IW ges","w\F P\IW r","w\F P\IW w","w\I P\IW ges","w\I P\IW r","w\I P\IW w"]
        table=[]
        for info in self.testInfo:
            filename=info["testname"]
            withISLaParseFormat=self.__get_test_result_name(GeneratedBy.FORMAT_FUZZER, filename, Testtypes.PARSE_WITH_ISLA.value)
            withFormatParseIsla=self.__get_test_result_name(GeneratedBy.ISLA, filename, Testtypes.PARSE_WITH_FORMAT_FUZZER.value)
            withFormatParseFormat=self.__get_test_result_name(GeneratedBy.FORMAT_FUZZER, filename, Testtypes.PARSE_WITH_FORMAT_FUZZER.value)
            withFormatParseIslaWrong=self.__get_test_result_name(GeneratedBy.ISLA_WRONG, filename, Testtypes.PARSE_WITH_FORMAT_FUZZER.value)
            withIslaParseIslaWrong=self.__get_test_result_name(GeneratedBy.ISLA_WRONG, filename, Testtypes.PARSE_WITH_ISLA.value)

            content=[filename]
            self.addContent(withISLaParseFormat, content)
            self.addContent(withFormatParseIsla, content)
            self.addContent(withFormatParseFormat, content)
            self.addContent(withFormatParseIslaWrong, content)
            self.addContent(withIslaParseIslaWrong, content)
            table.append(content)

        varname=self.__get_test_result_name(GeneratedBy.PARENT_TOOL, None, Testtypes.COLLECT_RESULTS.value)
        
        maxNameLen=0
        for val in table:
            maxNameLen=max(maxNameLen, len(val[0]))


        with open(varname, 'w') as witeTo_file:
            headers[0]=f"{{:<{maxNameLen}}}".format(headers[0])
            print(["{:<11}".format(a) for a in headers], file=witeTo_file)
            for line in table:
                line[0]=f"{{:<{maxNameLen}}}".format(line[0])
                print(["{:<13}".format(a) for a in line], file=witeTo_file)


    def run_tests(self):
        #create test directory
        if not os.path.exists(f"./{self.testDir}"):
            os.makedirs(f"./{self.testDir}")

        print("______________handle speed tests")
        for info in self.testInfo:
            self.__prepare_generate_files_test(self.langageName,self.GRAMMAR,info["constr"])
            for i in range(self.number_of_iteration):
                self.generate_files_by_ISLA_test(info["constr"], info["testname"], self.GRAMMAR,info["predicates"], i, negate_isla_flag=True )
                self.generate_files_by_ISLA_test(info["constr"], info["testname"], self.GRAMMAR,info["predicates"], i, negate_isla_flag=False )
                self.__generate_files_by_FORMAT_FUZZER_test(info["testname"], self.langageName, i )

        print("______________handle parse FORMAT FUZZER tests")
        for i in range(self.number_of_iteration):
            for info in self.testInfo:

                 self.__parse_with_ISLA_test(info["constr"], info["testname"], self.GRAMMAR, i, GeneratedBy.FORMAT_FUZZER,info["predicates"])
                 self.__parse_with_ISLA_test(info["constr"], info["testname"], self.GRAMMAR, i, GeneratedBy.ISLA_WRONG,info["predicates"])
                #find out how many files format fuzzer fuzzed wrong:
                 self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.FORMAT_FUZZER,info["constr"])

                

        print("______________handle parse with FORMAT FUZZER tests")
        for info in self.testInfo:
            for i in range(self.number_of_iteration):
                print("______begin parse correct files")
                self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.ISLA,info["constr"])
                print("______begin parse incorrect files")
                self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.ISLA_WRONG,info["constr"])
               
    
        print("______________handle k-path test for ISLa and FORMAT FUZZER")
    
        for info in self.testInfo:
            for i in range(self.number_of_iteration):
                self.__test_k_path_coverage(info["testname"], self.GRAMMAR,GeneratedBy.ISLA,i)
                self.__test_k_path_coverage(info["testname"], self.GRAMMAR,GeneratedBy.FORMAT_FUZZER,i)
                

        self.collect_results()
        #self.get_latex_tikzpicture_from_kpath()



    def __print_completed_info(self,testType,filename, iteration):
        date_time = datetime.now().strftime("%d/%m/%Y %H:%M:%S")
        print(f"{testType.value}_{iteration}: {filename} completed; {date_time}")

    def __get_directory(self,testType,filename, iteration=None, generated_by=None):
        name=f"./{self.testDir}/{filename}"
        if(iteration!=None): name+=f"/_iter{iteration}"
        return name+f"/{testType.value}"+(f"/{generated_by.value}" if generated_by else "")

    def __get_test_result_name(self,generated_by, filename, testType, iteration=""):
        fileInfo=f"{filename}/" if filename else ""
        return f"./{self.testDir}/{fileInfo}{testType}_{generated_by.value}{iteration}"

    def __prepare_generate_files_test(self,grammar_name,GRAMMAR,constr):
        #clear all used directories
        command = "rm -r -f ./output/*; rm -r -f ./input/*; rm -r -f ./l_isla/*; "
        subprocess.run(command, capture_output=False, shell=True)
        #exec file mit dem proposed tool    
        with open(f'./input/{grammar_name}.json', 'w', encoding='utf-8') as f:
            json.dump(GRAMMAR, f, ensure_ascii=False, indent=4)
        with open(f'./l_isla/{grammar_name}.json', 'w', encoding='utf-8') as f:
            f.write(constr)
        command = "python3 convert.py >/dev/null"
        subprocess.run(command, capture_output=False, shell=True)

        command = f"mv ./output/{grammar_name}.bt  ../FormatFuzzer/templates"
        subprocess.run(command, capture_output=False, shell=True)


        # führe format fuzzer mit bt files aus
        command = f"cd ../FormatFuzzer; ./build.sh {grammar_name} >/dev/null"
        subprocess.run(command, capture_output=False, shell=True)

    def __get_file_ending(self, generated_by):
        if(generated_by==GeneratedBy.ISLA):
            return "_is.test"
        elif(generated_by==GeneratedBy.FORMAT_FUZZER):
            return "_bt.test"
        elif(generated_by==GeneratedBy.ISLA_WRONG):
            return "_is_wrong.test"
        else:
            raise ValueError("notDefined")



    def generate_files_by_ISLA_test(self,constr, filename, GRAMMAR, predicates,iteration, negate_isla_flag):
        
        #prepare file ending and constraint
        testType=GeneratedBy.ISLA_WRONG if negate_isla_flag else GeneratedBy.ISLA
        fileEnding=self.__get_file_ending(testType)
        constraint=constr
        if(negate_isla_flag):
            constraint = - parse_isla(constraint, GRAMMAR,predicates)

        i=0
        solver = ISLaSolver(GRAMMAR, constraint,structural_predicates=predicates)
        if(filename=="no_redef_constr" and not negate_isla_flag):
            solver = ISLaSolver(
                GRAMMAR,
                constraint,
                structural_predicates=predicates,
                enforce_unique_trees_in_queue=True,
                cost_computer=GrammarBasedBlackboxCostComputer(
                    CostSettings(
                        CostWeightVector(
                            tree_closing_cost=5,
                            constraint_cost=2,
                            derivation_depth_penalty=6,
                            low_k_coverage_penalty=2,
                            low_global_k_path_coverage_penalty=21,
                        ),
                        k=3,
                    ),
                    gg.GrammarGraph.from_grammar(GRAMMAR),
                    reset_coverage_after_n_round_with_no_coverage=100,
                ),
            )


        res_dir=self.__get_directory(Testtypes.GENERATE_FILES,filename,iteration)
        if not os.path.exists(f"{res_dir}"):
            os.makedirs(f"{res_dir}")
        f_res = open(f"{res_dir}/{testType.value}_timing", "a+")
        start = time.time()
        while time.time() - start < self.generate_files_time:
            try:
                startTest=time.time()
                inp=solver.solve()
                f = open(f"{i}{fileEnding}", "a")
                f.write(f"{inp.__str__()}\n")
                f.close()
                end_test=time.time() - startTest 
                f_res.write(f"test{i}: {end_test}\n")
                i+=1
            except:
                print("generation of isla file went wrong")
        f_res.close()
        self.__print_completed_info(Testtypes.GENERATE_FILES,filename,iteration)


        

        dir=self.__get_directory(Testtypes.GENERATE_FILES,filename,iteration, testType)

        if not os.path.exists(f"{dir}"):
            os.makedirs(f"{dir}")
        fileEnding=self.__get_file_ending(testType)
        command = f"echo ./*{fileEnding} | xargs mv -t {dir} --"
        subprocess.run(command, capture_output=False, shell=True)
    
    def __generate_files_by_FORMAT_FUZZER_test(self, filename, grammar_name,iteration):

        fileEnding=self.__get_file_ending(GeneratedBy.FORMAT_FUZZER)
        i=0
        res_dir=self.__get_directory(Testtypes.GENERATE_FILES,filename,iteration)
        if not os.path.exists(f"{res_dir}"):
            os.makedirs(f"{res_dir}")

        f_res = open(f"{res_dir}/{GeneratedBy.FORMAT_FUZZER.value}_timing", "a+")
        start = time.time()
        while time.time() - start < self.generate_files_time:
            start_exec=time.time()
            command = f"../FormatFuzzer/{grammar_name}-fuzzer fuzz {i}{fileEnding} >/dev/null"
            subprocess.run(command, capture_output=False, shell=True)
            end_exec=time.time()-start_exec
            f_res.write(f"test{i}: {end_exec}\n")
            i+=1  
        f_res.close()
        self.__print_completed_info(Testtypes.GENERATE_FILES,filename, iteration)
        
        dir=self.__get_directory(Testtypes.GENERATE_FILES,filename,iteration, GeneratedBy.FORMAT_FUZZER)
        if not os.path.exists(f"{dir}"):
            os.makedirs(f"{dir}")

        command = f"echo ./*{fileEnding} | xargs mv -t {dir} --"
        subprocess.run(command, capture_output=False, shell=True)



    def parse_with_Format_Fuzzer_test(self,filename, grammar_name, iteration, generated_by, constr):
        self.__prepare_generate_files_test(self.langageName,self.GRAMMAR,constr)
        write_to_file=self.__get_test_result_name(generated_by, filename, Testtypes.PARSE_WITH_FORMAT_FUZZER.value)
        with open(write_to_file, 'a') as f:
            print(f"_____WRONG PARSED:", file=f)


        #copy files to test
        fileEnding=self.__get_file_ending(generated_by)
        dir=self.__get_directory(Testtypes.GENERATE_FILES,filename,iteration, generated_by)
        #print("thats my dir: ",dir)
        command = f"rm ../FormatFuzzer/*{fileEnding}"
        subprocess.run(command, capture_output=False, shell=True)
        command = f"cp {dir}/*{fileEnding}  ../FormatFuzzer"
        subprocess.run(command, capture_output=False, shell=True)

        
        false=0
        i=0
        while ( os.path.exists(f"../FormatFuzzer/{i}{fileEnding}")):

            #remove last newline
            if(generated_by==GeneratedBy.ISLA or generated_by==GeneratedBy.ISLA_WRONG):
                with open(f"../FormatFuzzer/{i}{fileEnding}", 'rb+') as f:
                    f.seek(-1, os.SEEK_END)
                    f.truncate()

            command = f"cd ../FormatFuzzer; ./{grammar_name}-fuzzer parse {i}{fileEnding}"
            result=subprocess.run(command, capture_output=True, shell=True)
            if(result.stderr.endswith("failed\n".encode('utf-8')) or result.stderr.endswith("(core dumped)\n".encode('utf-8'))):
                false+=1
                if(generated_by!=GeneratedBy.ISLA_WRONG):
                    with open(write_to_file, 'a') as f:
                        print(f"{i}{fileEnding}; err: {result.stderr}", file=f)
            else:
                if(generated_by==GeneratedBy.ISLA_WRONG):
                    with open(write_to_file, 'a') as f:
                        print(f"{i}{fileEnding}; err: {result.stderr}", file=f)
            #print(f"{i} parsed with FormatFuzzer")
            i+=1
        with open(write_to_file, 'a') as f:
            print(f"_____RESULTS:", file=f)
            print(f"Ammount parsed: {i}", file=f)
            print(f"Ammount parsed right: {i-false}", file=f)
            print(f"Ammount parsed wrong: {false}", file=f)
        self.__print_completed_info(Testtypes.PARSE_WITH_FORMAT_FUZZER,filename, iteration)
                
    def __parse_with_ISLA_test(self,constr, filename, GRAMMAR, iteration, generated_by,predicates):
        write_to_file=self.__get_test_result_name(generated_by, filename, Testtypes.PARSE_WITH_ISLA.value)
        dir=self.__get_directory(Testtypes.GENERATE_FILES,filename, iteration, generated_by)
        with open(write_to_file, 'a') as f:
            print(f"_____WRONG PARSED:", file=f)

        fileEnding=self.__get_file_ending(generated_by)

        false=0
        i=0
        sys.setrecursionlimit(4000)
        while ( os.path.exists(f"{dir}/{i}{fileEnding}")):
            f = open(f"{dir}/{i}{fileEnding}", "r")
            inp=f.read()
            if(inp[-1]=="\n"):
                inp=inp[:-1]
            try:
                tree = DerivationTree.from_parse_tree(next(EarleyParser(GRAMMAR).parse(inp)))
                eval_result=evaluate(constr, reference_tree=tree, grammar=GRAMMAR, structural_predicates=predicates)
                if (not eval_result and generated_by!=GeneratedBy.ISLA_WRONG) or eval_result and generated_by==GeneratedBy.ISLA_WRONG:
                    false+=1
                    with open(write_to_file, 'a') as f:
                        print(f"{i}{fileEnding}", file=f)
            except:
                if( not generated_by==GeneratedBy.ISLA_WRONG):
                    false+=1
                    with open(write_to_file, 'a') as f:
                        print(f"{i}{fileEnding}", file=f)
            #print(f"{i} parsed with isla")
            i+=1



        with open(write_to_file, 'a') as f:
            print(f"_____RESULTS:", file=f)
            print(f"Ammount parsed: {i}", file=f)
            print(f"Ammount parsed right: {i-false}", file=f)
            print(f"Ammount parsed wrong: {false}", file=f)
        self.__print_completed_info(Testtypes.PARSE_WITH_ISLA,filename, iteration)
 

    def __test_k_path_coverage(self,filename, GRAMMAR,generator_used,iteration):
        graph = GrammarGraph.from_grammar(GRAMMAR)
        fileEnding=self.__get_file_ending(generator_used)
        data=[]
        common_k_paths=set()
        all_k_paths=graph.k_paths(k=3, include_terminals=False)# -> all k-pahts of grammar

        dir=self.__get_directory(Testtypes.GENERATE_FILES,filename, iteration, generator_used)
        i=0
        while ( os.path.exists(f"{dir}/{i}{fileEnding}")):
            f = open(f"{dir}/{i}{fileEnding}", "r")
            inp=f.read()
            if(inp[-1]=="\n"):
                inp=inp[:-1]
        
            try:
                tree = DerivationTree.from_parse_tree(next(EarleyParser(GRAMMAR).parse(inp)))
                k_path_curr_test=tree.k_paths(graph, k=3) # -> all k-pahts for one test
                common_k_paths.update(k_path_curr_test)# -> unites k-paths with those from previous tests
                curr_coverage=round(len(common_k_paths)/len(all_k_paths),3)# -> get percentage coverage
                data.append(curr_coverage)
            except:
                print("file parsed wrong")
            i+=1

        write_to_file=self.__get_test_result_name(generator_used, filename, Testtypes.KPATH_COVERAGE.value,iteration)
        with open(write_to_file, 'w') as f:
            print(data, file=f)
