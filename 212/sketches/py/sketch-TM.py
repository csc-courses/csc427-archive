#!/usr/bin/env python
# coding: utf-8

# ### Turing Machine Programming
# 
# csc427: Theory of Automata and Complexity. 
# <br>
# university of miami
# <br>
# spring 2021.
# <br>
# Burton Rosenberg.
# <br>
# <br>
# created: 21 March 2020
# <br>last update: 5 April 2021
# 
# ***
# 

# ### TuringMachine class

# In[1]:


import string
import sys
import os
import argparse
import re

#
# tm-sim.py
#
# author: bjr
# date: 21 mar 2020
# last update: 22 mar 2020
#    16 mar 2021, updated 
#     3 apr 2021, return conventions for accept/reject
#                 verbose_levels reimplemented
#                 character # is not allowed as a tape symbol
#                 for magical reasons, then " is also not allowed
#                 added class method help()
#                 
#
# copyright: Creative Commons. See http://www.cs.miami.edu/home/burt
#

# GRAMMAR for the TM description

# Comments (not shown in BNF) begin with a hash # and continue to the end
#    of the line
# The ident tokens are states
# The symbol tokens are tape symbolss
# The StateTransition semantics is:
#     tape_symbol_read tape_symbol_written action new_state
# The underscore _ is a tape blank:
# The : in a transition rule is the default tape symbol match when there is no
#    exactly matching transition rule; in the target section of the rule it 
#    is the value of the matchined tape symbol.

# A missing transition is considered a reject, not an error

class TuringMachine:
    
    verbose_levels = {'none':0,'verbose':1,'explain':2, 'debug':3}
    result_reasons = ['ok', 'transition missing', 'time limit']

    grammar = """
    M-> (Stanza [emptyline])*
    Stanza-> StartStanza | AcceptStanza | RejectStanza | StateStanze
    StartStanza-> "start" ":" ident
    AcceptStanza-> "accept" ":" ident ([newline] [indent] ident])*
    RejectStanza-> "reject" ":" ident ([newline] [indent] ident])*
    StateStanze-> "state" ":" ident ([newline] [indent] StateTransition)+
    StateTransition-> (symbol|special) (symbol|special) action ident
    action-> l|r|n|L|R|N
    symbol-> \w[!$-/]     # note: a tape symbol
    special-> ":"
    ident-> \w+           # note: name of a state

    """

    def __init__(self):
        self.start_state = "" # is an state identifier
        self.accept_states = set() # is a set of state identifiers
        self.reject_states = set() # is a set of state identifiers
        self.transitions = {} # is a map of (state,symbol):(state,symbol,action)
        self.current_state = "" 
        self.step_counter = 0
        self.all_actions = ["r","l","n"]
        self.tape = ['_']  # is a list of symbols
        self.position = 0
        self.verbose = 0
        self.result = 0

    def set_start_state(self,state):
        self.start_state = state

    def set_tape(self,tape_string):
        self.tape =  ['_' if symbol==':' or symbol==' ' else 
                          symbol for symbol in tape_string]

    def add_accept_state(self,state):
        self.accept_states.add(state)

    def add_reject_state(self,state):
        self.reject_states.add(state)
    
    def get_current_state(self):
        return self.curent_state

    def add_transition(self,state_from,read_symbol,
                       write_symbol,action,state_to):

        if action.lower() not in self.all_actions:
            # return something instead, nobody likes a chatty program
            return "WARNING: unrecognized action."
        x = (state_from, read_symbol)
        if x in self.transitions:
            # return something instead, nobody likes a chatty program
            return "WARNING: multiple outgoing states not allowed for DFA's."
        self.transitions[x] = (state_to,write_symbol,action)
        return None

    def restart(self,tape_string):
        self.current_state = self.start_state
        self.position = 0
        if len(tape_string)==0 :
            tape_string = '_'
        self.set_tape(tape_string)
        self.step_counter = 1

    def step_transition(self):
        c_s = self.current_state
        x = (c_s,self.tape[self.position])
        
        if x in self.transitions:
            (new_state, symbol, action ) = self.transitions[x]
        elif (c_s,':') in self.transitions:
            # wildcard code
            (new_state, symbol, action ) = self.transitions[(c_s,':')]
        else:
            # here we implement a rejection of convenience, if there is
            # no transition, tansition target is (:, n, A_REJECT_STATE)
            self.reason = 1
            return False
        
        # wildcard code
        if symbol==':':
            symbol = self.tape[self.position]

        self.current_state = new_state
        self.tape[self.position] = symbol

        shout = False
        if action.lower() != action:
            shout = True
            action = action.lower()
        
        if action == 'l' and self.position>0:
            self.position -= 1
        if action == 'r':
            self.position += 1
            if self.position==len(self.tape):
                self.tape[self.position:] = '_'
        if action == 'n':
            pass
   
        if shout or self.verbose == TuringMachine.verbose_levels['explain']:
            self.print_tape()
        if self.verbose == TuringMachine.verbose_levels['debug']:
            print("\t", self.step_counter, "\t", new_state, symbol, action)
            
        self.step_counter += 1
        return True

    def compute_tm(self,tape_string,step_limit=0,verbose='none'):
        self.verbose = TuringMachine.verbose_levels[verbose]
        self.result = 0
        self.restart(tape_string)
        if self.verbose == TuringMachine.verbose_levels[verbose]:
            self.print_tape()
        step = 0
            
        stop_states = self.accept_states.union(self.reject_states)
        while self.current_state not in stop_states:
            res = self.step_transition()
            if not res:
                # missing transition is considered a reject
                return False
            step += 1
            if step > step_limit:
                self.result = 2 
                return None
            
            if self.verbose == TuringMachine.verbose_levels['debug']:
                print(step, self.current_state, self.position, self.tape )

        if self.current_state in self.accept_states:
            return True
        return False

    def print_tape(self):
        t, p = self.tape, self.position
        s = ''.join(t[:p] + ['['] + [t[p]] + [']'] + t[p+1:])
        print(f'{self.current_state}:\t{s}')
    
    def print_tm(self):
        print("\nstart state:\n\t",self.start_state)
        print("accept states:\n\t",self.accept_states)
        print("reject states:\n\t",self.reject_states)
        print("transitions:")
        for t in self.transitions:
            print("\t",t,"->",self.transitions[t])
    
    @classmethod
    def help(cls):
        print('The verbose levels are:')
        for level in cls.verbose_levels:
            print(f'\t{cls.verbose_levels[level]}: {level}')
        print()
        print('The grammar for the Turing Machine description is:')
        print(cls.grammar)
        
        
### end class TuringMachine


class MachineParser:

    @staticmethod
    def turing(tm_obj, fa_string):
        """
        Code to parse a Turing Machine description into the Turing Machine object.
        """
        
        fa_array = fa_string.splitlines()
        line_no = 0 
        current_state = ""
        in_state_read = False
        in_accept_read = False
        in_reject_read = False

        for line in fa_array:
            while True:

                # comment lines are fully ignored
                if re.search('^\s*#',line):
                    break

                if re.search('^\s+',line):

                    if in_state_read:
                        m = re.search('\s+(\w|[!$-/:])\s+(\w|[!$-/:])\s+(\w)\s+(\w+)',line)
                        if m:
                            res = tm_obj.add_transition(current_state,
                                    m.group(1),m.group(2),m.group(3),m.group(4))
                            if res: 
                                print(res, f'line number {line_no}')
                                return False
                            break

                    if in_accept_read:
                        m = re.search('\s+(\w+)',line)
                        if m:
                            tm_obj.add_accept_state(m.group(1))
                            break

                    if in_reject_read:
                        m = re.search('\s+(\w+)',line)
                        if m:
                            tm_obj.add_reject_state(m.group(1))
                            break

                in_state_read = False
                in_accept_read = False
                in_reject_read = False

                # blank lines do end multiline input
                if re.search('^\s*$',line):
                    break ;

                m = re.search('^start:\s*(\w+)',line)
                if m:
                    tm_obj.set_start_state(m.group(1))
                    break

                m = re.search('^accept:\s*(\w+)',line)
                if m:
                    tm_obj.add_accept_state(m.group(1))
                    in_accept_read = True
                    break

                m = re.search('^reject:\s*(\w+)',line)
                if m:
                    tm_obj.add_reject_state(m.group(1))
                    in_reject_read = True
                    break

                m = re.search('^state:\s*(\w+)',line)
                if m:
                    in_state_read = True
                    current_state = m.group(1)
                    break

                print(line_no,"warning: unparsable line, dropping: ", line)
                return False
                break

            line_no += 1
        return True

### end class MachineParser


# In[2]:



def create_and_test_turing_machine(tm_description, test_cases,verbose='none'):
    tm = TuringMachine()
    MachineParser.turing(tm,tm_description)
 
    print("\n*** TEST RUNS ***")

    for s in test_cases:
        # assume complexity is some quadratic
        res = tm.compute_tm(s,step_limit=10*(len(s)+5)**2,verbose=verbose)
        if res==True:
            print(f'ACCEPT input {s}\n')
        elif res==False:
            print(f'REJECT input {s}\n')
        else:
            print(f'ERROR on input {s}: {TuringMacine[tm.result]}')
            
    print("\n\n*** RUN COMPLETE ***\n\n")

TuringMachine.help()


# ### Examples
# 
# 
# 
# 

# #### Machine M1, the language of twin strings.
# 
# From the alphabet <code>{ 0, 1, &amp; }</code> accept all strings of the 
# form <code>w &amp; w</code> with <code>w &isin; { 0, 1 }<sup>*</sup></code>.
# 
# We are programming Turing Machines as a proof by example that a Turing Machine is at least as powerful as a typically architectured computer (the RAM model of computation). The method of programing Turing Machines has a few tactics. Some facts can be remembered in the state, but most facts need to be remembered by markings on the tape. This sample program uses both sorts of memory. 
# 
# We remember we are matching a 0, respectively a 1, but transition into a state "saw a 0, needing to match a 0", respectively "saw a 1, needing to match a 1". What we characters have been matched is recorded by "marking" the character as being done. We do that in this case by overwriting it with an "x". 
# 
# <div style="padding:01.5em 5em;">
# <code>
# LOOP INVARIANT:
#      At the top of the loop the tape configuration is,
#         x<sup>i</sup> U &amp; x<sup>i</sup> V
#     with the head over the leftmost character in U. 
#     Furthermore the original w can be written as w' U with len(w')=i.
#     Update: (i, U, V) &mapsto; (i+1, U[1:], V[1:])  if U[0]==V[0].
# </code>
# </div>
# 
# 

# In[7]:



# Turing Machine M1, Sipser 3ird ed page 173, Sipser 2nd ed page 145

tm_M1 = """# the language of twin strings
# w&w   w in {0,1}*

start: q1
accept: A
reject: R

state: q1
    0 x r q2 # remember a 0
    & : r q8 # left exhausted
    1 x r q3 # remember a 1

state: q2
    0 : r q2 # going right ...
    1 : r q2 # until we find ...
    & : r q4 # the ampersand
    
state: q4
    x : r q4 # going right until we find ...
    0 x l q6 # the matching 0
    
state: q3
    0 : r q3 # going right ...
    1 : r q3 # until we find ...
    & : r q5 # the ampersand
    
state: q5
    x : r q5 # going right until we find ...
    1 x l q6 # the matching 1

state: q6
    0 : l q6 # go left ...
    1 : l q6 # go left ...
    x : l q6 # go left ...
    & : l q7 # until the ampersand is found
    
state: q7
    0 : l q7 # go left ...
    1 : l q7 # go left ...
    x : r q1 # until an x is found 

state: q8
    x : r q8 # is everything matched?
    _ : r A  # yes. accept

"""

tm_M1_test = [
    "&",
    "10&10",
    "000&000",
    "000&001",
    "00&000",
    "000&00",
    "0&",
    "&0"
]

create_and_test_turing_machine(tm_M1,tm_M1_test,verbose='explain')  
    


# In[4]:



# Turing Machine M2, Sipser 3ird ed page 172, Sipser 2nd ed page 144

tm_M2 = """#  The language of the powers of 2, in unary.
# 0^(2^n) n >= 0


start: q1
accept: A
reject: R

state: q1
    _ : r R
    x : r R
    0 _ r q2
    
state: q2
    x : r q2
    _ : r A
    0 x r q3
    
state: q3
    x : r q3
    _ : l q5
    0 : r q4
    
state: q4
    x : r q4
    _ : r R
    0 x r q3
    
state: q5
    0 : l q5
    x : l q5
    _ : r q2

"""


tm_M2_test = [
    "0",
    "00",
    "000",
    "0000",
    "00000",
    "000000",
    "00000000",
    "0000000000"
]

create_and_test_turing_machine(tm_M2,tm_M2_test,verbose='explain')  
  


# In[5]:



# Turing Machine M3, Sipser 3ird ed page 174, Sipser 2nd ed page 146

tm_M3 = """# The language of multiplication
# a^i b^j c^k, i,j,k >=1, and k = i*j

# a student assignment 

"""


# In[6]:



# Turing Machine M4, Sipser 3ird ed page 175, Sipser 2nd ed page 147

tm_M4 = """# The language of distinct elements
# &x1&x2&...&xk where each xi in {0,1}*, and xi != xj for each i != j

# student assignment 
# note: the book says to place a mark on top of a &. let the tape symbol for a
# "marked" & be a %.

"""


# In[ ]:




