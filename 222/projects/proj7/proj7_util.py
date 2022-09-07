#
# name: proj7_util.py
# created for csc427.222 univ of miami
# helper functions for project 7
#
# last-udate:
#     28 mar 2022: created from code in proj7.ipynb
#
#

import re
from turing_machine_sim import *

def basic_test_mt_add(tm_description, test_cases, verbose='explain'):

    def match_number(s):
        re_pat_nonzero = "^(&[01]*1)0*(-?)_*$"
        re_pat_zero = "^&0+_*$"
        if re.search(re_pat_zero,s):
            return "&0"
        else:
            m = re.search(re_pat_nonzero,s)
            if m: return m[1]+m[2]
        return False

    tm = MachineParser.create_from_description(tm_description)
    correct = 0
    incorrect = 0
    exception = 0
    
    # true cases
    for (s_in,s_out) in test_cases[0]:

        print(f'\ninput:\t|{s_in}|')
        # assume complexity is some quadratic
        res = tm.compute_tm(s_in,step_limit=10*(len(s_in)+5)**2,verbose=verbose)
        if tm.is_exception():
            print(f'** exception!')
            exception += 1
            continue
        if res!=True:
            print(f'** reject!')
            incorrect += 1
        else:
            t = tm.get_tape()
            s = match_number(t)
            print(f'output:\t|{t}|')
            if not s:
                print(f'** bad format!')
                incorrect += 1
            if s == s_out:
                correct += 1
                print('** correctly calculated')
            else:
                incorrect += 1
                print(f'** wrong answer! expected |{s_out}|')
                
    for s in test_cases[1]:
        print(f'\ninput:\t|{s}|')
        res = tm.compute_tm(s,step_limit=250*(len(s)+20)**2,verbose=verbose)
        if tm.is_exception():
            print(f'** exception!')
            exception += 1
            continue
        if res!=False:
            print(f'** accepted! (should have been rejected)')
            incorrect += 1
        else:
            print('** correctly rejected')
            correct += 1

    print(f'\ncorrect: {correct}, incorrect: {incorrect}, exceptions: {exception}')
    return incorrect == 0 and exception == 0

def convert_to_int(s):
    place = 1
    tot = 0
    for c in s:
        if c=="1": tot += place
        place *= 2
    return tot

