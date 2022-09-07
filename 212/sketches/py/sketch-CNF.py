#!/usr/bin/env python
# coding: utf-8

# ## Sketch: Chomsky Normal Form
# 
# _author: burton rosenberg_
# 
# _date: february 2021_
# 
# _last update: 20 march 2021;_
# - alternative reduction, to reduce the size of the created grammar.
# - see Richard Cole, 2007: https://cs.nyu.edu/courses/fall07/V22.0453-001/cnf.pdf
# 

# ### Class ChomskyNormal
# 
# The class takes a grammar as a dictionary, with special requirements on the variables and terminals, and reduces it to Chomsky Normal Form.
# 
# There are several steps to the reduction.
# 
# __Lifting the Start State:__ A new start state is created, with the rule new start reduces to original start. If the empty string is part of the language, this new start state is alone permitted an epsilon rule.
# 
# __Epsilon removal:__ All epsilon rules are eliminated. If the rule "E to :" appears, it is removed, and all rules with E on the right-hand-side are adjusted. This might produce new epsilon rules, which are then iteratively removed.
# 
# __Unit Rule removal:__ All unit rules are eliminated. If the rule "A to B" appears, it is removed, and for each unit rule "B to C" found, the rule rule "A to C" is added. This might create new unit rules, which are then iteratively removed.
# 
# __Bring to Form:__ This consists of two sub-tasks. Given a rule "A to u", replace all terminals in u with a variable that reduces to that terminal, and if u is of length greater than two, use chaining variables to create a sequence of rules, each of length two, which exactly replicate the effect of u.
# 
# Sipser carries out these steps in the order presented. However, this can lead to a CNF exponentially larger than the original grammar. We also present another order, that seems to lead to a CNF of size linear in the original grammar.
# 
# 
# ### Definition specification
# 
# 
# The CNG is presented as a dictionary with,
# 
# - key "variables", a list of variables
# - key "terminals", a list of terminals
# - key "rules", a dictionary of variable:list(strings of variables and terminals)
# - key "start", a variable
# 
# The variables and terminals are strings with these special rules, 
# 
# 1. The characters %, _ and : are reserved. 
# 2. The : character represents the empty string.
# 3. They are either a single non-reserved character, or the _ character followed by a % character string of non-reserved characters.
# 
# With the additional reservation that, 
# 
# 4. Strings of the second form, when the % enclosed string is all digits, is reserved.
# 

# In[10]:


from inspect import currentframe as frame_cur , getframeinfo as frame_get
import re

debug = False
explain = True

"""
author: bjr
last-update: 
    1 march 2021 - rewritten for rule type dict string:set (tuple(strings*))
    18 march 2021 - added explain feature
    
"""

# reduce to chomsky normal form

# parse the grammar into dict of string:set( tuple(string^i) ), 
# where i = 0, 1, 2, ... and where string is matches [^_%:]|_%[^_%:]*%
# note, case i = 0 represents the empty string

# input rules are list(string), where string matches ([^_%:]|_%[^_%:]*%)+ or :

class ChomskyNormal:
    
    def __init__(self,grammar):
        
        def check_symbols():
            pat = re.compile('[^%_:]|_%[^%_:]*%')
            for v in self.variables:
                assert re.fullmatch(pat,v)
            for t in self.terminals:
                assert re.fullmatch(pat,t)
            assert self.variables.isdisjoint(self.terminals)
            assert self.start in self.variables
            
        def parse_rule(rule):
            if len(rule)==0 or rule==':':
                return tuple()
            pat = re.compile('[^%_:]|_%[^%_:]*%')
            pat2 = re.compile('([^%_:]|_%[^%_:]*%)+')
            assert re.fullmatch(pat2,rule)
            w = tuple(re.findall(pat,rule))
            return w

        self.variables = set(grammar['variables'])
        self.terminals = set(grammar['terminals'])
        self.start = grammar['start']
        
        check_symbols()
        
        self.rules = {}
        for key in grammar['rules']:
            self.rules[key] = set()
            for rule in grammar['rules'][key]:
                self.rules[key].add(parse_rule(rule))

        self.count = 0

    def next_variable(self):
        v = '_%'+str(self.count)+'%'
        self.count += 1
        return v

    def remove_epsilon(self):
       
        def init_queue():
            q = []
            for s in self.variables:
                if s == self.start or s not in self.rules:
                    continue
                if tuple() in self.rules[s]:
                    self.rules[s].remove(tuple())
                    q.append(s)
                    if explain:
                        print(f'\tRemove rule {s} -> :')
            return q

        def rm_from_rule(key,variable,rule):
            # rule is a tuple of strings, variable is a string
            # remove occurrances of variable in the tuple, in all 
            # combinations.
            
            new_rules = set([rule])
            q = []
            q.append(rule)
            while q:
                w = q[0]
                del q[0]
                for i in range(len(w)):
                    if w[i]==variable:
                        w1 = w[:i]+w[i+1:]
                        if w1 not in new_rules:
                            new_rules.add(w1)
                            q.append(w1)
                            if explain:
                                w2 = ''.join(w1)
                                if len(w2)==0:
                                    w2 = ':'
                                print(f'\tAdd rule {key} -> {w2}')
            return new_rules

        if explain:
            print(f'(2) Remove epsilon rules:')
        
        q = init_queue()
        if debug: 
            print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno})',q)
            
        i = 0
        while len(q)>i:
            s = q[i]
            # eps remove if s->'' is a rule
            for key in self.rules:
                new_rules = set()
                for rule in self.rules[key]:
                    new_rules |= rm_from_rule(key,s,rule)
                # do the new rules have an eps?
                if key != self.start and tuple() in new_rules:
                    new_rules.remove(tuple())
                    if explain:
                        print(f'\tRemove rule {key} -> :')
                    if key not in q:
                        q.append(key)
                self.rules[key] |= new_rules
            i += 1   

    def remove_unit(self):

        # q is a list of unit rules A->B represented as ('A',('B',))
        # start by sweeping through the rules and putting all found unit rules on q
        
        # walk through q and for each unit rule A->B as it appears on q,
        #    remove the rule A->B 
        #    and for all B->u add the rule A->u
        
        #    if the unit rule A->C is added, check if it is anywhere on q
        #    and if not, add it to the end of q
        
        def is_unit_rule(r):
            return len(r)==1 and r[0] in self.variables
        
        def init_queue():
            q = []
            for lhs in self.rules:
                for rhs in self.rules[lhs]: 
                    if is_unit_rule(rhs):
                        q.append((lhs,rhs))
            return q

        if explain:
            print(f'(3) Remove unit rules:')

        q = init_queue()
        i = 0 
        while len(q)>i:
            (lhs,rhs) = q[i]
            if debug: 
                print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno})', f'unit rule: {lhs}->{rhs}')

            self.rules[lhs].remove(rhs)
            if explain:
                rhs_s = ''.join(rhs)
                print(f'\tRemove rule {lhs} -> {rhs_s}')
            if rhs[0] in self.rules:
                for rule in self.rules[rhs[0]]:
                    if debug: 
                        print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno})', 
                              f'because of {rhs[0]}->{rule} add rule {lhs}->{rule}')

                    self.rules[lhs].add(rule)
                    if explain:
                        rhs_s = ''.join(rule)
                        print(f'\tAdd rules {lhs} -> {rhs_s}')
                    if is_unit_rule(rule) and (lhs,rule) not in q:
                        q.append((lhs,rule))
            i += 1

    def bringto_form(self):
        
        # rules transformed to A->a or A->BC. 
        
        # lift_terminals will replace terminals in long patterns with a 
        # variable reducing to that terminal. 
        # a dictionary keeps track of these variables, for reuse.
        
        # once all terminals lifted, new variables fold longer patterns
        # into two variables, by an iterative reduction from the pattern end.
             
        
        def lift_terminals(rule):
            if debug:
                print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno}){rule} becomes ',end='')

            rule = list(rule)
            for i in range(len(rule)):
                if rule[i] in self.terminals:
                    if rule[i] not in terminals:
                        u = self.next_variable()
                        terminals[rule[i]] = u
                        self.rules[u] = set([tuple(rule[i])])
                        if explain:
                            print(f'\tAdd rule {u} -> {rule[i]}')
                    rule[i] = terminals[rule[i]]
            
            rule = tuple(rule)
            if debug:
                print(f'({rule})')         
            return rule

        if explain:
            print(f'(4) All rules to CNF:')

        terminals = {}
        chaining_variables = []
        for v in self.variables:
            if v in self.rules:
                new_rules = set()
                for rule in self.rules[v]:
                    
                    if len(rule)>1:
                        rule = lift_terminals(rule)
                        
                    while len(rule)>2:
                        u = self.next_variable()
                        chaining_variables.append(u)
                        self.rules[u] = set([rule[-2:]])
                        if explain:
                            rule_2 = ''.join(rule[-2:])
                            print(f'\tAdd rule {u} -> {rule_2}')
                        rule = rule[:-2]+(u,)
                        
                    if explain:
                        rule_2 = ''.join(rule)
                        if len(rule_2)==0:
                            rule_2 = ':'
                        print(f'\tAdd rule {v} -> {rule_2}')

                    new_rules.add(rule)

                self.rules[v] = new_rules

        for t in terminals:
            self.variables.add(terminals[t])
            
        self.variables |= (set(chaining_variables))

    def lift_start(self):
        new_start =  self.next_variable()
        if explain:
            print(f'(1) New start:\n\tAdd rule {new_start} -> {self.start}')
        self.rules[new_start] = set([(self.start,)])
        self.start = new_start
        self.variables.add(new_start)
        
    def reduce(self):
        self.lift_start()
        if debug:
            print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno}) after start lift:',self.rules)
        self.remove_epsilon()
        if debug:
            print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno}) after epsilon remove: ',self.rules)
        self.remove_unit()
        if debug:
            print(f'({frame_get(frame_cur()).function}:{frame_get(frame_cur()).lineno}) after unit remove',self.rules)
        self.bringto_form()
        
    def reduce_alt(self):
        """
        The 4 stages of the reduction, 
        (1) lifting the start, 
        (2) removing the epsilon rules,
        (3) removing the unit rules, 
        (4) bringing the rules to form, 
        can be done in different order to avoid the grammar increasing in size
        exponentially.
        
        Doing (4) before (2), followed by (3) will produce a new grammar linear in size
        with the old grammar.
        """
        self.lift_start()
        self.bringto_form()
        self.remove_epsilon()
        self.remove_unit()
        
    def get_grammar(self):
        cfg = {
            'variables':self.variables,
            'terminals':self.terminals,
            'rules':{},
            'start':self.start
        }
        for k in self.rules:
            cfg['rules'][k] = []
            for rule in self.rules[k]:
                # each rule is a tuple
                if rule==tuple():
                    cfg['rules'][k].append(':')
                else:
                    cfg['rules'][k].append(''.join(rule))
        return cfg
    
    def describe(self,banner="Context Free Grammar",grammar=None):
        print(f'\n*** {banner} ***')
        if grammar:
            d = grammar
        else:
            d = self.get_grammar()
        key = ['variables','terminals','start','rules',]
        for k in key:
            print(f'{k} ({len(d[k])} items):\n\t{d[k]}')


# ### Examples from the Sipser textbook

# In[2]:


cfg_G4 = {
    'variables':['E','T','F'],
    'terminals':['a','+','*','(',')'],
    'rules':{
        'E':['E+T','T'],
        'T':['T*F','F'],
        'F':['(E)','a']
    },
    'start':'E',    
}
cn = ChomskyNormal(cfg_G4)
cn.reduce()
cn.describe(grammar=cfg_G4)
#cn.describe(banner='Chomsky Normal Form')

cn = ChomskyNormal(cfg_G4)
cn.reduce_alt()
cn.describe(banner='Chomsky Normal Form')


# In[3]:


cfg_G5 = {
    'variables':['E'],
    'terminals':['a','+','*','(',')'],
    'rules':{
        'E':['a','E+E','E*E','(E)']
    },
    'start':'E',    
}
cn = ChomskyNormal(cfg_G5)
cn.reduce_alt()
cn.describe(grammar=cfg_G5)
cn.describe(banner='Chomsky Normal Form')


# In[4]:


cfg_G6 = {
    'variables':['S','A','B'],
    'terminals':['a','b'],
    'rules':{
        'S':['ASA','aB'],
        'A':['B','S'],
        'B':['b',':']
    },
    'start':'S',    
}
cn = ChomskyNormal(cfg_G6)
cn.reduce_alt()
cn.describe(grammar=cfg_G6)
cn.describe(banner='Chomsky Normal Form')


# In[5]:


# exercise 2.14 in 2nd ed Sipser
grammar = {
    'variables':['A','B'],
    'terminals':['0'],
    'rules':{
        'A':['BAB','B',''],
        'B':['00','']
    },
    'start':'A'
}

cn = ChomskyNormal(grammar)
cn.reduce_alt()
cn.describe(grammar=grammar)
cn.describe(banner='Chomsky Normal Form')


# ### Random Examples

# In[6]:


grammar = {
    'variables':['S','A','B','C'],
    'terminals':['a','b','c'],
    'rules':{
        'S':['aabbaacc']
    },
    'start':'S'
}

cn = ChomskyNormal(grammar)
cn.reduce_alt()
cn.describe(grammar=grammar)
cn.describe(banner='Chomsky Normal Form')


# In[7]:


grammar = {
    'variables':['S','A','B','C'],
    'terminals':['a','b','c'],
    'rules':{
        'S':[':','A','AB'],
        'A':['aA','a',':'],
        'B':['bB','b',':'],
    },
    'start':'S'
}

cn = ChomskyNormal(grammar)
cn.reduce()
cn.describe(grammar=grammar)
cn.describe(banner='Chomsky Normal Form')


# ### Test of alternative orders in the reduction

# In[11]:


grammar = {
    'variables':['S','X'],
    'terminals':['a','b','c','d','e','f','.'],
    'rules':{
        'S':['aXbXcXdXeXf'], 'X':['.',':']
    },
    'start':'S'
}

cn = ChomskyNormal(grammar)
cn.reduce()
cn.describe(grammar=grammar)
cn.describe(banner='Chomsky Normal Form')
cn = ChomskyNormal(grammar)
cn.reduce_alt()
cn.describe(banner='Chomsky Normal Form, alternative reduction')


# In[ ]:




