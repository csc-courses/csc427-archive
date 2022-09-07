#!/usr/bin/env python
# coding: utf-8

# ## Sketch: Pumping Lemmas
# 
# 
# _Burton Rosenberg_
# 
# _23 february 2021_
# 
# -----
# 
# 
# 
# 

# In[21]:


"""
The verbose switch:
    Set this true or false, to run code verbosely
"""

verbose = False


# ### Machine Model Modified
# 
# The MachineModel class, which implements a DFA from a DFA description, and has been used
# elsewhere in this class, is modified.
# 
# One modification is for it to count the number of times a state is achieved during a computation.
# 
# One finds a string s and a state q such that the state q is entered more than once during the
# computation of s. For the purposes of this demonstration, s should be accepted by the DFA.
# 
# A new method records the letter sequence that leads up to q the first time, the letter
# sequence that continues on to q the second time, and the sequence of remaining letters. 
# This is the break up s = x y z where y can be pumped.

# In[24]:


class MachineModel:
    """
    A machine description is a dictionary with,
        'states': a list of states.
        'alphabet': a list of letters (strings of length one)
        'transitions': a dictionary with keys tuples (a state,a letter) to a state
        'start': a state (the start state)
        'accept': a list of states (the accepting states)
        
    The states are any hashable, and we use:
    - strings for simple DFA's, 
    - tuples for product DFA's, 
    - and, in next week's problem set, frozensets for determinizing an NFA
        
    """
    
    def __init__(self,machine_description):
        self.states = machine_description['states']
        self.alphabet = machine_description['alphabet']
        self.transitions = machine_description['transitions']
        self.start_state = machine_description['start'] 
        self.accept_states = machine_description['accept']
        self.current_state = self.start_state 
        self.state_count = {}

    def do_transition(self,letter):
        self.current_state = self.transitions[(self.current_state,letter)]
    
    def compute(self,word,count_states=False):
        
        def incr_state_count(state):
            if state in self.state_count:
                self.state_count[state] += 1
            else:
                self.state_count[state] = 0
            
        if count_states: self.state_count = {}
        self.current_state = self.start_state
        incr_state_count(self.current_state)

        if verbose : print(self.current_state)
        for w in word:
            self.do_transition(w)
            incr_state_count(self.current_state)
            if verbose : print(w,self.current_state)
        if count_states:
            print('input:',word,'state count:',self.state_count)
        return self.current_state in self.accept_states

    def compute_pumping_parts(self,word,magic_state):
        ##
        ## find x, y, z such that word = xyz, and y begins 
        ## and ends on state magic_state
        ##
        self.current_state = self.start_state
        pumping = ['','','']
        pump_part = 0
        if verbose : print(self.current_state)
        for w in word:
            if self.current_state == magic_state and pump_part<2:
                pump_part += 1
            pumping[pump_part] += w
            self.do_transition(w)
            if verbose : print(w,self.current_state)
        return pumping       
        
    def describe(self,name=""):
        print("Machine Description:",name)
        print("\tstates:",len(self.states))
        for s in self.states:
            print("\t\t",s)
        print("\ttransitions:",len(self.transitions))
        for t,v in self.transitions.items():
            print(f"\t\t{t}  ->  {v}")
        print("\taccept states:",len(self.accept_states))
        for a in self.accept_states:
            print("\t\t",a)
        print()


def test_machine(dfa_description,test_cases,name="",count_states=False):
    
    print('running tests ...')
    dfa = MachineModel(dfa_description)
    if verbose: dfa.describe(name)
    for (t,r) in (test_cases):
        if dfa.compute(t,count_states) != r:
            print(r,'\t|'+t+'|','\tWRONG, ABORT')
            return False
        print(r,'\t|'+t+'|','\tOK')
    return True
  


# ### Example A:
# 
# The problem 1.5(b) DFA from Sipser 2nd edition, is an example.

# In[23]:


## all w such that w continas baba

dfa_1_5b = {
    'states':['1','2','3','4','5'],
    'alphabet':['a','b'],
    'transitions':{
        ('1','a'):'1',('1','b'):'2',
        ('2','a'):'3',('2','b'):'2',
        ('3','a'):'1',('3','b'):'4',
        ('4','a'):'5',('4','b'):'2',
        ('5','a'):'5',('5','b'):'5',
    },
    'start':'1',
    'accept':['5']
}

test_cases = [
    ('baba',True),
    ('bab',False),
    ('aaababaa',True),
    ('aaabba',False),
    ('babbabbababb',True),
    ('babbabbabbab',False),
]

def pumping_test(dfa_def,word,magic_state,max_pump=5):
    dfa = MachineModel(dfa_def)
    if not dfa.compute(word):
        print(word,'is not in the language')
        return
    (x,y,z) = dfa.compute_pumping_parts(word,magic_state)
    print('pumping decomposition on state',magic_state)
    print('\t'+x+'|'+y+'|'+z)
    y_1 = ''
    for i in range(max_pump):
        print('pump:',i)
        print('\t'+x+'|'+y_1+'|'+z)
        print('\t'+str(dfa.compute(x+y_1+z)))
        y_1 += y
    print()

#test_machine(dfa_1_5b,test_cases,count_states=True)

dfa = MachineModel(dfa_1_5b)
dfa.compute('babbabbababb',count_states=True)

pumping_test(dfa_1_5b,'babbabbababb','3')
pumping_test(dfa_1_5b,'babbabbababb','2')


# ### Example B:
# 
# The problem 1.4(b) DFA from Sipser 2nd edition, is an example.

# In[17]:



## all strings w such that it has an een number of a's and each a is followed by at least one b

dfa_1_4b = {
    'states':['1','2','3','4','5'],
    'alphabet':['a','b'],
    'transitions':{
        ('1','a'):'4',('1','b'):'1',
        ('2','a'):'5',('2','b'):'1',
        ('3','a'):'2',('3','b'):'3',
        ('4','a'):'5',('4','b'):'3',
        ('5','a'):'5',('5','b'):'5',
    },
    'start':'1',
    'accept':['1']
}

dfa = MachineModel(dfa_1_4b)
dfa.compute('bbabbabb',count_states=True)
dfa.compute('bbbbabbbabbb',count_states=True)
pumping_test(dfa_1_4b,'bbbbabbbabbb','3')

dfa.compute('bbabbabbabababab',count_states=True)
pumping_test(dfa_1_4b,'bbabbabbabababab','4')
pumping_test(dfa_1_4b,'bbabbabbabababab','2')


# In[ ]:




