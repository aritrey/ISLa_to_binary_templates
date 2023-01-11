    #these functions can be used for additional tests or debugging. if you want to use them, insert them to the Tests class



    #generates a list with k-path coverage per single test case
    def __test_graph_k_paths_from_tree_no_terminals(self,filename, GRAMMAR,generator_used):
        graph = GrammarGraph.from_grammar(GRAMMAR)
        fileEnding=self.__get_file_ending(generator_used)

        data=[]
        common_k_paths=set()
        all_k_paths=graph.k_paths(k=3, include_terminals=False)

        for iteration in range(self.number_of_iteration):
            dir=self.__get_directory(Testtypes.GENERATE_FILES,filename, iteration, generator_used)
            i=0
            while ( os.path.exists(f"{dir}/{i}{fileEnding}")):
                filename_to_open=f"{dir}/{i}{fileEnding}"
                f = open(filename_to_open, 'r')
                input=f.read()
                if(generator_used!=GeneratedBy.FORMAT_FUZZER):
                    input=input[:-1]
            
                try:
                    tree = DerivationTree.from_parse_tree(next(EarleyParser(GRAMMAR).parse(input)))
                    k_path_curr_test=tree.k_paths(graph, k=5) 
                    common_k_paths.update(k_path_curr_test)
                    curr_coverage=round(len(common_k_paths)/len(all_k_paths),3)
                    data.append(curr_coverage)
                except:
                    print("file parsed wrong")
                i+=1
        #plt.hist(data)
        write_to_file=self.__get_test_result_name(generator_used, filename, Testtypes.KPATH_COVERAGE_5.value)
        
        with open(write_to_file, 'a') as f:
            print(f"__________result of all ({self.number_of_iteration}) iterations______________", file=f)
            print(f"OUTPUT DATA:{data}", file=f)
        #plt.hist(data, bins=100)
        #plt.savefig(f"{write_to_file}.png")
        self.__print_completed_info(Testtypes.KPATH_COVERAGE,filename, 0)




    #applies generated templates on older tests for parsing (use for debug when code was edited)
    def run_tests_vgl(self,testTokens):
        #create test directory
        for testToken in testTokens:#["28_12_2022__21_43_21","29_12_2022__14_58_25","30_12_2022__08_34_32"]:
            self.testDir=f"test_output/{testToken}/{self.langageName}"
         
            print("______________handle parse with FORMAT FUZZER tests")
            for info in self.testInfo:
                self.__prepare_generate_files_test(self.langageName,self.GRAMMAR,info["constr"])
                for i in range(self.number_of_iteration):
                    print("______begin parse correct files")
                    self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.ISLA,info["constr"])
                    print("______begin parse incorrect files")
                    self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.ISLA_WRONG,info["constr"])
                    self.parse_with_Format_Fuzzer_test( info["testname"],self.langageName,  i, GeneratedBy.FORMAT_FUZZER,info["constr"])
                



    #generates bt file for all specified tests in test_output/__constraint_fuer_vgl/{self.langageName}/ (use for debug when code was edited)
    def generate_bt_files_for_compare(self):
        if not os.path.exists(f"./{self.testDir}"):
            os.makedirs(f"./{self.testDir}")
            
        for info in self.testInfo:
            if not os.path.exists(f"./{self.testDir}"):
                os.makedirs(f"./{self.testDir}")
                    #clear all used directories
            command = "rm -r -f ./output/*; rm -r -f ./input/*; rm -r -f ./l_isla/*; "
            subprocess.run(command, capture_output=False, shell=True)
            #exec file mit dem proposed tool    
            with open(f'./input/{self.langageName}.json', 'w', encoding='utf-8') as f:
                json.dump(self.GRAMMAR, f, ensure_ascii=False, indent=4)
            with open(f'./l_isla/{self.langageName}.json', 'w', encoding='utf-8') as f:
                f.write(info["constr"])
            command = "python3 convert.py >/dev/null"
            subprocess.run(command, capture_output=False, shell=True)

            command = f"mv ./output/{self.langageName}.bt  test_output/__constraint_fuer_vgl/{self.langageName}/{info['testname']}_latest.bt"
            subprocess.run(command, capture_output=False, shell=True)
            



    #generated new templates and compares them to the former generated template in folder testtoken
    def compare_binary_template(self, testtoken):
        for info in self.testInfo:
            print(f"compare {info['testname']}:")
            command = "rm -r -f ./output/*; rm -r -f ./input/*; rm -r -f ./l_isla/*; "
            subprocess.run(command, capture_output=False, shell=True)
            #exec file mit dem proposed tool    
            with open(f'./input/{self.langageName}.json', 'w', encoding='utf-8') as f:
                json.dump(self.GRAMMAR, f, ensure_ascii=False, indent=4)
            with open(f'./l_isla/{self.langageName}.json', 'w', encoding='utf-8') as f:
                f.write(info["constr"])
            command = "python3 convert.py >/dev/null"
            subprocess.run(command, capture_output=False, shell=True)



            f1 = open(f"./output/{self.langageName}.bt","r")
            f2 = open(f"test_output/{testtoken}/{self.langageName}/{info['testname']}.bt","r")
            i = 0
            for line1 in f1:
                i += 1
                for line2 in f2:
                    if line1 != line2:  
                        #line is array
                        match_array=lambda x: re.match(r'[ \t]*local[ ]+(?:string|int)[ ]+([a-zA-Z0-9_]+)\[\][ ]*=[ ]*{((?:".*?", )*".*?")};[ \t]*', x)
                        result1 = match_array(line1)
                        result2 = match_array(line2)
                        if(result1 and result2):
                            same_name=result1.group(1)==result2.group(1)
                            same_elem=set(result1.group(2).split(", "))==set(result2.group(2).split(", "))
                            if(same_name and same_elem):
                                break

                        match_init=lambda x: re.match(r'[ \t]*struct [a-zA-Z0-9_]+\(string follow\[\], int size\){};[ \t]*', x) 
                        if(match_init(line1) and match_init(line2)):
                            break

                        is_comment=lambda x: re.match(r'^[ \t]*//.*',x)
                        if(is_comment(line1) and is_comment(line2)):
                            break

                        is_empty=lambda x: re.match(r'^[ \t]*$',x)
                        if(is_empty(line1) and is_empty(line2)):
                            break 
                        

                        print(f"Line {i}:")
                        print(f"\tFile old: '{line1}'", end="")
                        print(f"\tFile new: '{line2}'", end="")
                    break
            f1.close()                                       
            f2.close()  


    #generates latex tikzpicture from k-path data (k-path acumulated)
    def get_latex_tikzpicture_from_kpath(self):   # get k-pah coverage 
        print("begin grap k-path")
        for i in range(self.number_of_iteration):
            for generator_used in [GeneratedBy.ISLA,GeneratedBy.FORMAT_FUZZER]:
                f=open(self.__get_test_result_name(generator_used, None,Testtypes.KPATH_COVERAGE.value, iteration=i),"w")
                print("""\\begin{figure}

        \\begin{tikzpicture}
        \\begin{axis}[
        height=5cm,
        width=15cm,
        %ybar               = 2pt, % configures `bar shift'
        xmajorgrids        = true,
        %x tick label style={/pgf/number format/1000 sep=},
        %x tick label style={rotate=45,anchor=east},
        ylabel={generated output files},
        ylabel={files in percent},
        enlargelimits=true,
        ymin               = 0,
        ymax               = 1,
        bar width          = 4pt,
        legend style={at={(0.04,0.96)},anchor=north west},
    % nodes near coords=\rotatebox{90}{\pgfmathprintnumber\pgfplotspointmeta},
    %   nodes near coords style={font=\small}    
        ]

    """,file=f)
                for info in self.testInfo:  
                        filename=info["testname"]
                        write_to_file=self.__get_test_result_name(generator_used, filename, Testtypes.KPATH_COVERAGE.value, iteration=i)
                        str = open(write_to_file, 'r').read()
                        str=str[66:-2]
                        str_list=str.split(',')
                        if(str_list[-1][-1]=="]"):
                            str_list[-1]=str_list[-1][:-1]
                        print(write_to_file)
                        float_list=[float(x) for x in str_list]
                        
                        print(f"%{filename}\n\\addplot coordinates {{",file=f)
                        coverage1Seen=False
                        for idx, coverage in enumerate(float_list):
                            if(coverage==1.0 and coverage1Seen==False):
                                print(idx+1)
                                coverage1Seen=True
                            print(f"({idx+1},{coverage})",file=f)
                        
                        print(f"({len(float_list)},{float_list[-1]})")
                            
                        adjustedFileName=filename.replace("_", "-" )
                        print(f"}};\\addlegendentry{{{adjustedFileName}}}",file=f)
                        
                print(f"""
            \\end{{axis}}
            \\end{{tikzpicture}}

            \\caption{{{generator_used.value+"_"+self.langageName}}}
            \\label{{{"fig:"+generator_used.value+"_"+self.langageName}}}
        \\end{{figure}}""",file=f)
                f.close()



   # create tikzpicture addplot for k-path per 10%
    def run_tests_for_graph_alt(self, testtokens):   # get k-pah coverage 
        print("begin grap k-path")
        for info in self.testInfo:  
            for generator_used in [GeneratedBy.ISLA,GeneratedBy.FORMAT_FUZZER]:
                fileNames=[]
                resultArr=10*[0]
                for testToken in testtokens:
                    self.testDir=f"test_output/{testToken}/{self.langageName}"

                    filename=info["testname"]
                    write_to_file=self.__get_test_result_name(generator_used, filename, Testtypes.KPATH_COVERAGE.value)
                    str = open(write_to_file, 'r').read()
                    str=str.split("[")[1]
                    str=str.split("]")[0]
                    str_list=str.split(',')
                    print(str_list)
                    float_list=[float(x) for x in str_list]
                    
                    
                    for coverage in float_list:
                        #print(coverage)
                        #print(int(round(coverage*10, 0)))
                        #print(resultArr)
                        #print(resultArr[int(round(coverage*10, 0))])
                        listIndex=int(round(coverage*10, 0))
                        if(listIndex>=10):
                            listIndex=9
                        resultArr[listIndex]+=1

                filename=info["testname"]
                testedFiles=0
                for x in resultArr:
                    testedFiles+=x
                resultArrInPercent=[round(x/testedFiles*100, 1) for x in resultArr]

                #print(f"{filename}_____{generator_used.value}")          
                #print(f"abs val:    ",resultArr)       
                #print(f"in prozent: ",resultArrInPercent)
                print(f"%{filename}\n\\addplot coordinates {{")
                fileNames.append(filename)
                for idx, x in enumerate(resultArrInPercent):
                    begin=idx*10
                    end=begin+10
                    print(f"({begin}-{end},{x})")
                print("};")
            print(f"\\addlegendentry{{{','.join(fileNames)}}}")
                    
