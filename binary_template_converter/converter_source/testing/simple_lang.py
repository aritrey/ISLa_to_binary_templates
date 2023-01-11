from isla.isla_predicates import BEFORE_PREDICATE, IN_TREE_PREDICATE
from grammars import  SIMPLE_LANG
from test_functions import Tests



def test_simple_lang(testToken):


    forall_exists = """
forall <F> f1="({<E> e})":
    exists <F> f2 in e:
	(= f2 "a")"""
    exists_exists = """
exists <F> f1="({<E> e})":
    exists <F> f2 in e:
	(= f2 "a")"""
    exists_forall = """
exists <F> f1="({<E> e})":
    forall <F> f2 in e:
	(= f2 "a")"""
    forall_forall = """
forall <F> f1="({<E> e})":
    forall <F> f2 in e:
	(= f2 "a")"""

    inside_test = """
exists <F> f2:
    forall <F> f1="({<E> e})":
	((= f2 "a") and inside(f2, e))"""


    before_test = """
forall <F> f1="({<E> e})":
	exists <F> f2:
	((= f2 "a") and before(f2, e))
    """
    
    testInfo=[
        {
        "testname":"forall_exists",
        "constr":forall_exists,
        "predicates":set() 
        },
        {
        "testname":"exists_exists",
        "constr":exists_exists,
        "predicates":set() 
        },
        {
        "testname":"exists_forall",
        "constr":exists_forall,
        "predicates":set() 
        },
        {
        "testname":"forall_forall",
        "constr":forall_forall,
        "predicates":set() 
        },
        {
        "testname":"inside_test",
        "constr":inside_test,
        "predicates":{IN_TREE_PREDICATE}
        },
        {
        "testname":"before_test",
        "constr":before_test,
        "predicates":{BEFORE_PREDICATE}
        },
    ]

    langageName="SIMPLE_LANG"
    Tests(testInfo,SIMPLE_LANG, langageName, testToken).run_tests()