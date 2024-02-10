import numpy as np
import random

# This file contains an implementation of the DPLL (Davis-Putnam-Logemann-Loveland) algorithm for SAT problem solving


# Takes a .cnf file path and transforms it into a matrix 
def parse_cnf(file_path):
    with open(file_path, 'r') as file:
        lines = file.readlines()

    lines = [line.strip() for line in lines]
    lines = lines[1:]
    clauses = [list(map(int, line.split()[:-1])) for line in lines[1:]]

    return clauses


# Takes a CNF and a literal as input
# Returns true if the CNF is in the literal otherwise false

def lit_in_cnf(lit, cnf):
    for cl in cnf:
        if lit in cl:
            return True
    return False



# Takes a CNF in input
# Returns a list of unique pure literals of a CNF (all in positive)

def get_unique_literals(cnf):
    uniq = []
    for clause in cnf:
        for lit in clause:
            if lit not in uniq and -lit not in uniq:
                uniq.append(abs(lit))       
    return uniq

# Takes a cnf in input
# Uses MOMs heuristic to select the best literal
# Targets the literal that appears the most of times in the shortest clauses

def select_literal(cnf):
    literal_occurrences = {}
    for clause in cnf:
        for lit in clause:
            if lit not in literal_occurrences and lit_in_cnf(lit, cnf):
                literal_occurrences[lit] = 1
            literal_occurrences[lit] += 1

    best_literal = None
    num_occs = 0
    for key, val in literal_occurrences.items():
        if val > num_occs:
            num_occs = val
            best_literal = key
            
    return best_literal

# Takes a CNF and a literal in input
# Returns a simplified CNF : - Removes every clause that contains the literal (As it is satisfied now)
#                            - Removes the negation of the literal from every clause that contains it

def simplify(cnf, literal):
    simplified_cnf = []
    for clause in cnf:
        if -literal in clause:
            new_clause = clause[:]
            new_clause.remove(-literal)
            simplified_cnf.append(new_clause)
        elif literal in clause:
            continue
        else:
            simplified_cnf.append(clause)
            
    return simplified_cnf

# Takes a CNF in input
# Returns True if the CNF has an empty clause, returns False otherwise

def has_empty_clause(cnf):
    for clause in cnf:
        if len(clause)==0:
            return True
    return False

# Takes a CNF in input
# If the CNF has a unit clause :  returns True and the unit clause (If there are many, the first one encountered is returned)
# Else : Returns False, None

def has_unit_clause(cnf):
    bool_val = False
    lit = None
    for clause in cnf:
        if(len(clause)==1):
            bool_val = True
            lit = clause[0]
            break
    return bool_val, lit


# The recursive dpll function
# Takes the CNF and a valuation set to False on all variables by default
# Returns True if cnf is sat, returns False otherwise

def dpll(cnf, valuation):

    if(len(cnf)==0): # All clauses were removed => Formula is True (all clauses were satisfied)
        return True
        
    if(has_empty_clause(cnf)): # Empty clause means that a literal whose negation existed alone in a clause was chosen => formula can't be True 
        return False
    
    bool_val, lit_val = has_unit_clause(cnf)  # Here the algorithm checks if the CNF has any unit clauses
    
    if(bool_val==True): # If so then apply unit propagation on one of the unit clauses
        valuation[abs(lit_val)] = lit_val > 0
        return dpll(simplify(cnf, lit_val), valuation)
    
    literal = select_literal(cnf) # Select a False literal from the valuation (goes by order, no special prioritizing)

    
    valuation[literal] = True
    if dpll(simplify(cnf, literal), valuation): # If the call reaches a True (Empty CNF) then return True
        return True
    
    valuation[literal] = False  # Otherwise, the negation of the literal exists in unit clause, and the literal needs to be False
    return dpll(simplify(cnf, -literal), valuation) 
        

# A wrapper to mask the valuation as a local variable and to cutomize the output
# Takes the CNF as input
# Returns the valuation if the CNF is sat, returns None otherwise (unsat)

def dpll_wrapper(cnf):
    valuation = {}
    P = get_unique_literals(cnf)
    for p in P:
        valuation[p] = False
    
    sat = dpll(cnf, valuation)
    
    if(sat == True):
        print("SATISIFIABLE")
        print(valuation)
        return valuation
    
    print("UNSATISFIABLE")
    return None



# These CNF's were tested using : https://www.inf.ufpr.br/dpasqualin/d3-dpll/ 
cnf1 = [[1, 2], [-1, 2], [-2, 3], [-3, 4], [-4, 1]] #sat Expect : {1: True, 2: True, 3: True, 4: True}

cnf2 = [[1, 2], [-1, -2], [1, -2]] #sat Expect : {1: True, 2: False}

cnf3 = [[1, 2], [-1, -2], [-1, 3], [-3, 4], [4, -2]] #sat Expect : {1: True, 2: False, 3: True, 4: True}

cnf4 = [[1, 2], [-1, -2], [1, -2], [-1, 2]] #unsat

cnf5 = [[1, 2, 3], [1, -2, 3], [-1, -3], [2, -3]] #sat Expect : {1: True, 2: False, 3: False}

cnf6 =  [[1, -2], [-1, 2], [1, -2], [-1, 2]] #sat Expect : {1: True, 2: True}

cnf7 = [[1, -2, 3], [-1, 2, 3], [1, -3], [2, -3], [-1, -2]] # sat Expect : {1: False, 2: False, 3: False}

cnf8 =  [[1, 2], [-1, -2], [-1, 2], [1, -2]] #unsat

cnf10 = [[1],[-1]]


cnf_path = 'test.cnf'
file_path = 'example.cnf'
cnf_formula = parse_cnf(cnf_path)

# https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html this website contains good CNF lists that can be used for test
# I tested my code with some of them and it worked very well

dpll_wrapper(cnf_formula)


# By Farouk Soufary
# Computer Science student specializing in Artificial Intelligence
# @ENSEIRB-MATMECA