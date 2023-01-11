


from datetime import datetime
from script_size_c import test_script_size_c
from simple_lang import test_simple_lang


if __name__ == '__main__':    
    testToken=datetime.now().strftime("%d_%m_%Y__%H_%M_%S")
    test_script_size_c(testToken)
    test_simple_lang(testToken)
