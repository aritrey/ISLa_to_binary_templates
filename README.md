# Bachelor Thesis: Conversion of ISLa Constraints into Binary Templates

## Dependencies

The only required dependency is an environment which is able to run docker containers and has access to docker-compose.

## Build instructions
- Make sure you are in the root of the project.
- If you want to run the script as non-root user, create a docker group, add your current user to it and login to the group:
```
sudo groupadd docker
sudo usermod -aG docker $USER
newgrp docker
```



### On Linux
- $ ./build.sh

## Usage
- Make sure you are in the root of the project
- The run script takes as input:
    - a Context-free grammar of Json format in ./input
     (The script clears the output folder for each run)
    - an ISLa constraint in  ./l_isla
- The result will be found in the folder ./output

- examples of grammars and corresponding ISLa coonstraints can be found in ./testoutput

### On Linux
- $ ./run.sh


## Tests

### Running on Linux
- $ ./run_tests.sh\
! Attention ! The script overwrites the files in the following folders: 
    - ./input 
    - ./l_isla 
    - ./output\
! Attention ! Even with a runtime of one minute during generation, the script runs for over 24 hours at average computing power. 

sample grammars with test can be found in the folder ./grammars_with_constraints

### The results
The results of the tests are saved in the folder
./test_output/<dd_mm_yyy__hh_mm_ss>
where the subfolder represents the date and time of the test start.


#### RQ1: Time Efficiency
Results in ./test_output/<dd_mm_yyy__hh_mm_ss>/[SIMPLE_LANG|SCRIPT_SIZE_C]/collect_results_parent_tool (arithmetic mean of all test runs)

'w\\\\F P\\\\F ges': Number of generated files by Format Fuzzer\
'w\\\\F P\\\\I ges': Number of generated files by ISLa solver

#### RQ2: Generation Diversity
Results in ./test_output/<dd_mm_yyy__hh_mm_ss>/[SIMPLE_LANG|SCRIPT_SIZE_C]/k_paths_test_[formatFuzzer|isla]\<i\>, where \<i\> is the number of the test run

Every value in the array shows the resulting k-path coverage after a new file was created. The last value is the resulting k-path coverage after one minute.

#### RQ3: Precision as Generator
Results in ./test_output/<dd_mm_yyy__hh_mm_ss>/[SIMPLE_LANG|SCRIPT_SIZE_C]/collect_results_parent_tool (arithmetic mean of all test runs)

'w\\\\I P\\\\F ges': Total number of files generated\
'w\\\\I P\\\\F R  ': correctly generated files (100% expected)\
'w\\\\I P\\\\F W  ': wrongly generated files (0% expected (for the simple language))

(Files generated invalidly by Format Fuzzer but detected by itself are to be found in 'w\\\\F P\\\\F W '. For the complex language Format Fuzzer is likely to abort file creation. Therefore subtract 'w\\\\F P\\\\F W ' from 'w\\\\I P\\\\F W ' to receive wrongly generated files that were not aborted generations).

#### RQ4: Accuracy as Parser
Results in ./test_output/<dd_mm_yyy__hh_mm_ss>/[SIMPLE_LANG|SCRIPT_SIZE_C]/collect_results_parent_tool (arithmetic mean of all test runs)

Parsing of the correctly generated files:\
'w\\\\F P\\\\I ges': total number of parsed tests\
'w\\\\F P\\\\I R  ': correctly parsed files (100% expected)\
'w\\\\F P\\\\I W  ': incorrectly parsed files (0% expected)

Parsing of the incorrectly generated files:\
'w\\\\F P\\\\I ges': total number of parsed tests\
'w\\\\F P\\\\I R  ': detected as correct by format fuzzer (0% expected)\
'w\\\\F P\\\\I W  ': detected as incorrect by format fuzzer (100% expected)

(For the test cases "forall-exists" and "inside-test" substract 'w\\\\I P\\\\IW w ' from 'w\\\\F P\\\\IW r ' to get the real number of values detected as incorrect by format fuzzer. 'w\\I P\\IW w ' is the number of wrongly generated tests by the ISLa solver with the negated constraint. These numbers are created by parsing the generated files for the negated constraint with the ISLa solver.)


More detailed information about which files were parsed incorrectly can be found in the folders for the respective tests.

### Modification of the tests
#### Runtime for the generation of the files:
 - one minute by default
 - can be changed: in attribute generate_files_time of Tests class in file binary_template_converter/converter_source/testing/test_functions.py <a/>
#### Iterations of the tests:
 - three by default
 - can be changed: in the attribute number_of_iteration of the Tests class in the file binary_template_converter/converter_source/testing/test_functions.py 
#### Test less constraints:
By commenting out elements in the "testInfo" array in ./binary_template_converter/converter_source/testing/simple_lang.py ./binary_template_converter/converter_source/testing/script_size_c.py
can be used to exclude individual tests from generation.

