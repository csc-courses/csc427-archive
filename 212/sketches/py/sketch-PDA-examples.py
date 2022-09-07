#!/usr/bin/env python
# coding: utf-8

# ## Sketch: Push Down Automata
# 
# _burton rosenberg_
# 
# _last update:_
# 
# - 26 feb 2021, created
# - 2 march 2021, a sketch
# - 10 march 2021, arranged for presentation
# 
# ------

# ## PDA Description Format
# 
# 
# __PDA Description:__
# 
#     A PDA description is a dictionary with,
#     
#         'states': a list of states.
#         'alphabet': a list of word letters
#         'symbols': a list of stack symbols
#         'transitions': a dictionary of
#                 tuple(state,alphabet_e,symbols_e):list(tuple((state,symbols_e)))
#         'start': a state (the start state)
#         'accept': a list of states (the accepting states)
#   
#     A state is a string
#     A word letter is a string of length 1, but not the string ':'
#     A stack symbol is a string but not the string ':'
#     alphabet_e is alphabet adjoining ':'
#     symbols_e is the symbols adjoining ':'
#     The string ':' is used in transtitions to denote the empty string.
# 

# In[1]:


"""
The verbose switch:
    Set this true or false, to run code verbosely
"""

verbose = True


# In[2]:


class MachineModelPDA:
    """
    A machine description is a dictionary with,
        'states': a list of states.
        'alphabet': a list of word letters
        'symbols': a list of stack symbols
        'transitions': a dictionary of
                tuple(state,alphabet_e,symbols_e):list(tuple((state,symbols_e)))
        'start': a state (the start state)
        'accept': a list of states (the accepting states)
  
    a state is a string
    a word letter is a string of length 1, but not the string ':'
    a stack symbol is a string but not the string ':'
    alphabet_e is alphabet adjoining ':'
    symbols_e is the symbols adjoining ':'
    
    and extended state (ext_state) is the tuple (state,location,stack contents)
    the stack contents is a tuple of symbols, with the top of the stack at index 0,
    
    the current state is a list of extended states, each extended state the result of 
    computing up to but not including the index in the word given by the integer "location" .
    
    """
    
    def __init__(self,machine_description):
        
        def check_transitions():
            ## check that it is a dict((state,alapha_e,symbols_e):list((state_symbols_e)))
            assert type(self.transitions)==type({})
            for k in self.transitions:
                assert k[0] in self.states
                assert k[1]==':' or k[1] in self.alphabet
                assert k[2]==':' or k[2] in self.symbols
                vs = self.transitions[k]
                assert type(vs)==type([])
                for v in vs:
                    assert v[0] in self.states
                    assert v[1]==':' or v[1] in self.symbols
        
        def check_alphabet():
            ## the alphabet symbols must be single characters,
            ## and should not be the : character which has the special
            ## meaning of a possible non-input consuming transition.
            for a in self.alphabet:
                assert len(a)==1 and a != ':'
                
        def check_start():
            assert self.start_state in self.states
            
        def check_accept_states():
            assert type(self.accept_states)==type([])
            for s in self.accept_states:
                assert s in self.states
        
        self.states = machine_description['states']
        self.alphabet = machine_description['alphabet']
        self.symbols = machine_description['symbols']
        self.transitions = machine_description['transitions']
        self.start_state = machine_description['start'] 
        self.accept_states = machine_description['accept']
        
        check_transitions()
        check_alphabet()
        check_start()
        check_accept_states()
        
        # for the non-deterministic trace we need to have the complete state, 
        # including stack contents and current input location
        self.current_states = [(self.start_state,0,())]
        
        # hint list. this works for verification
        self.merlin = []


    def do_transition(self,word,current_state):
        
        def trans_aux(letter,new_i,state,symbol,stack):
            new_states = []
            key = (state,letter,symbol)
            if key in self.transitions:
                for new_state,new_symbol in self.transitions[key]:
                    if new_symbol != ':':
                        nstack = (new_symbol,)+stack
                    else:
                        nstack = stack
                    new_states.append((new_state,new_i,nstack))
            return new_states
            
        state, i, stack = current_state
        new_states = []
        
        # transition of input letter
        if i<len(word):
            if len(stack)>0:
                new_states.extend(trans_aux(word[i],i+1,state,stack[0],stack[1:]))
            new_states.extend(trans_aux(word[i],i+1,state,':',stack))

        # epsilon transitions
        if len(stack)>0:
            new_states.extend(trans_aux(':',i,state,stack[0],stack[1:]))
        new_states.extend(trans_aux(':',i,state,':',stack))
        
        return set(new_states)  # glean duplicates of possible states
        
    def approximate_compute(self,word,limit):
        
        ## returns True if word is in language, False if it is not,
        ## and None if the computation was terminated and did not
        ## determine membership.
        
        def word_accepted():
            for ext_state in self.current_states:
                state, i, stack = ext_state
                if i==len(word) and state in self.accept_states:
                    return True
            return False
        
        self.current_states = set([(self.start_state,0,())])
        for steps in range(limit):
            
            if verbose: print(self.current_states)
            if word_accepted():
                return True
            if len(self.current_states)==0:
                return False

            new_states = set()
            for ext_state in self.current_states:
                new_states |= self.do_transition(word,ext_state)
            self.current_states = new_states
            if (len(self.current_states)>limit*limit):
                return None
            
        return None   # computation abandoned
        
        
    def describe(self,name=""):
        print("Machine Description:",name)
        print("\tstates:",len(self.states))
        print("\t\t",self.states)
        print("\tsymbols:",len(self.symbols))
        print("\t\t",self.symbols)
        print("\ttransitions:",len(self.transitions))
        for t,v in self.transitions.items():
            print(f"\t\t{t}  ->  {v}")
        print("\taccept states:",len(self.accept_states))
        print("\t\t",self.accept_states)
        print()


def test_machine(pda_description,test_cases,name="",limit=100):
    
    print('running test:',name)
    pda = MachineModelPDA(pda_description)
    if verbose: pda.describe(name)
    for (t,r) in (test_cases):
        if pda.approximate_compute(t,limit) != r:
            print(r,'\t|'+t+'|','\tWRONG, ABORT')
            return False
        print(r,'\t|'+t+'|','\tOK')
    print("** passes test")
    return True
  


# ## Examples:
# 
# Follows are example PDA programs for the three examples in the class textbook. 
# 
# 1. The language 0<sup>i</sup>1<sup>i</sup> for all non-negative i,
# 2. The language a<sup>i</sup>b<sup>j</sup>c<sup>k</sup> where either i=j or i=k,
# 3. The language ww<sup>R</sup>, where the superscript R means the word string rewritten backwards.

# In[6]:


## sipser figure 2.15; 0^n1^n

pda_2_15 ={
    'states':['1','2','3','4'],
    'alphabet':['0','1'],
    'symbols':['$','0'],
    'transitions':{
        ('1',':',':'):[('2','$')],
        ('2','0',':'):[('2','0')],('2','1','0'):[('3',':')],
        ('3','1','0'):[('3',':')],('3',':','$'):[('4',':')]
    },
    'start':'1',
    'accept':['4','1']
}



test = [
    ('',True),
    ('01',True),
    ('0011',True),
    ('0000011111',True),
    ('1',False),
    ('001',False),
    ('00111',False),
    ('00011111',False),
    ('10',False),
    ('1010',False)
]
test_machine(pda_2_15,test,name="0^n1^n")


# In[8]:


## a^i b^j c^k with i==j or i==k sipser 2nd edition figure 2.17

pda_2_17 = {
    'states':['1','2','3','4','5','6','7'],
    'alphabet':['a','b','c'],
    'symbols':['$','A'],
    'transitions':{
        ('1',':',':'):[('2','$')],
        ('2','a',':'):[('2','A')],('2',':',':'):[('3',':'),('5',':')],
        ('3','b','A'):[('3',':')],('3',':','$'):[('4',':')],
        ('4','c',':'):[('4',':')],
        ('5','b',':'):[('5',':')],('5',':',':'):[('6',':')],
        ('6','c','A'):[('6',':')],('6',':','$'):[('7',':')],
    },
    'start':'1',
    'accept':['4','7']
}

test = [
    ('',True),
    ('ab',True),
    ('ac',True),
    ('abc',True),
    ('abbc',True),
    ('abcc',True),
    ('abbcc',False),
    ('abcabc',False),
    ('aaabccc',True),
    ('aaabbbc',True),
    ('aaabbccca',False)
]
test_machine(pda_2_17,test,name="a^ib^jc^k, i==j or i==k")


# In[7]:


## w w^R, sipser figure 2.19

pda_2_19 = {
    'states':['1','2','3','4'],
    'alphabet':['0','1'],
    'symbols':['$','0','1'],
    'transitions':{
        ('1',':',':'):[('2','$')],
        ('2','0',':'):[('2','0')],('2','1',':'):[('2','1')],('2',':',':'):[('3',':')],
        ('3','0','0'):[('3',':')],('3','1','1'):[('3',':')],('3',':','$'):[('4',':')],
    },
    'start':'1',
    'accept':['4','1']
}
test = [
    ('',True),
    ('11',True),
    ('00',True),
    ('0110',True),
    ('1001',True),
    ('11000011',True),
    ('1100110011',True),
    ('1',False),
    ('0',False),
    ('1100',False),
    ('0011',False),
    ('0101',False),
    ('1010',False),
    ('00011001',False),
    ('1111111',False)
]
test_machine(pda_2_19,test,name="w w^r")


# ## More Examples:
# 
# Some "tamer" CLF's. Some that are RE's without the need for a stack, and some that have no need for non-determinism because strings include hints inside them.
# 

# In[3]:


## accepts the language {"abc"}

pda_abc = {
    'states':['A','B','C','D'],
    'alphabet':['a','b','c'],
    'symbols':['X','Y','Z'],
    'transitions':{
        ('A','a',':'):[('B','X')],
        ('B','b',':'):[('C','Y')],
        ('C','c',':'):[('D','Z')],
    },
    'start':'A',
    'accept':['D']
}

test = [
    ('abc',True),
    ('abd',False),
    ('aaa',False)
]
test_machine(pda_abc,test,name="language: {abc}")


# In[4]:


## ab*a

pda_a_b_star_a = {
    'states':['S','A1','A2'],
    'alphabet':['a','b'],
    'symbols':[],
    'transitions':{
        ('S','a',':'):[('A1',':')],
        ('A1','b',':'):[('A1',':')],('A1','a',':'):[('A2',':')],
        },
    'start':'S',
    'accept':['A2']
}

test = [
    ('aa',True),
    ('aba',True),
    ('abbbba',True),
    ('ab',False),
    ('abbb',False),
    ('abbbbbbab',False)
]
test_machine(pda_a_b_star_a,test,name="language: {ab*a}")


# In[5]:


## accepts a deterministic reversal language, w c w^R were w in {a,b}*

pda_wcwr = {
    'states':['S','W','WR','A'],
    'alphabet':['a','b','c'],
    'symbols':['$','A','B'],
    'transitions':{
        ('W','a',':'):[('W','A')],('W','b',':'):[('W','B')],
        ('W','c',':'):[('WR',':')],
        ('WR','a','A'):[('WR',':')],('WR','b','B'):[('WR',':')],
        ('S',':',':'):[('W','$')],('WR',':','$'):[('A',':')]
    },
    'start':'S',
    'accept':['A']
}

test = [
    ('abcba',True),
    ('aaacaaa',True),
    ('bbbbcbbbb',True),
    ('aabbcbbaa',True),
    ('abcab',False),
    ('abcaa',False),
    ('abacabaa',False),
    ('abacab',False),
]
test_machine(pda_wcwr,test,name="language: WcW^R")


# In[ ]:




