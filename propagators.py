#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

 ##############################################################################################################
def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
   
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar): #return list of constraints that include var in their scope 
        if c.get_n_unasgn() == 0: #return the number of unassigned variables in the constraint's scope
            vals = []
            vars = c.get_scope() #get list of variables the constraint is over QQQQ What does this mean???
            for var in vars:
                vals.append(var.get_assigned_value()) #return assigned value...returns None if is unassigned
            if not c.check(vals): #Returns true iff the value assignments satisfy the constraint
                return False, []
    return True, []
###############################################################################################################

def FCcheck(c, unassigned_vars, pruny):
    #unassigned_var is not assigned, C (constraint) does not have it assigned
    vals = []
    vars = c.get_scope() #get list of variables the constraint is over
    #l_removed = []
    #for var in vars: #for v belonging to dom(V)
    #   vals.append(var.get_assigned_value()) #Assign (v, V)
    for var in vars:
        vals.append(var.get_assigned_value()) #Make our list of previous assignments
    #Loop through and check if vals are None
    for v in range(len(vals)):
        if vals[v] == None:
            indexy = v #Where we append the unassigned variable together with the previous assignments
            break

    for val in unassigned_vars.cur_domain():
        vals[indexy] = val 
        if not c.check(vals):
            if (pruny.count((unassigned_vars, val)) == 0): #Check if we have pruned it already
                unassigned_vars.prune_value(val)
                pruny.append(tuple((unassigned_vars, val)))
    if unassigned_vars.cur_domain_size() == 0:
        return False, pruny #Domain Wipe out

    return True, pruny
    #We have our domain V

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
       #Place Constraint on Queue Q
       #For each "almost bound" constraint, C, let V denote the unassigned variable
       #For each v belonging to domV
       #    Assign v to V
       #    If C is violated, remove v from dom V
       #    If domV = 0, them a domain wipe-out has occured, and we must backtrack to the previous partial assignment
    pruner = []
    D_wipe_out = True
    if not newVar: #We look for unary constraints with one remaining variable (scope == 1) FORWARD CHECK ALLLL CONSTRAINTS
        conny = csp.get_all_cons()
    else:
        conny = csp.get_cons_with_var(newVar) #ONLY FORWARD CHECK CONSTRAINTS CONTAINING NEWVAR
    for c in conny: #return list of constraints that does include var
        #Check if list of variables the constraint is over
        if (c.get_n_unasgn() == 1): #If scope is 1 in length len is never 1 though?????
            unassigned_var = c.get_unasgn_vars() #There is only going to be one
            D_wipe_out, pruner = FCcheck(c, unassigned_var[0], pruner) #If check does not work
        if D_wipe_out == False:
            return False, pruner #unassign
                
    return True, pruner

class Queue:
    def __init__(self):
        self.q = []

    def dequeue(self):
        return self.q.pop() #pop from last object last object should be the oldest one

    def enqueue(self, value):
        self.q.insert(0, value) #Put at the beginning

    def size(self):
        return len(self.q)

    def isin(self, value):
        if self.q.count(value) > 0:
            return True
        else:
            return False
    
    def empty_queue(self):
        while self.q != []:
            self.dequeue()


def GAC_enforce(csp, gac_queue, prune):
    while gac_queue.size() != 0:
        constraint = gac_queue.dequeue() #Dequeue a constraint
        
        for i in constraint.get_scope(): #for 
            for v in i.cur_domain():
                #If not satisfiable
                if constraint.has_support(i, v) == False: #See if theey are not satisfiable
                    #remove v from domain
                    prune.append((tuple((i, v))))
                    i.prune_value(v)
                    #If curDomain is empty and V = v is inconsistent
                    if i.cur_domain_size() == 0:
                        gac_queue.empty_queue()
                        return False, prune
                    else:
                        for c in csp.get_cons_with_var(i):
                            if (gac_queue.isin(c) == False):
                                gac_queue.enqueue(c)
    return True, prune
                    




def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
    processing all constraints. Otherwise we do GAC enforce with
    constraints containing newVar on GAC Queue'''
    GAC_queue = Queue()
    pruner = []
    D_wipe_out = True
    if not newVar:
        #Do initial GAC enforce processing all constraints
        for con in csp.get_all_cons(): #return list of constraints that include var in their scope 
            #For each constraint C whose scope contains V we put it on the GAC_queue
            GAC_queue.enqueue(con)
        D_wipe_out, pruner = GAC_enforce(csp, GAC_queue, pruner)
        if D_wipe_out == False:
            return False, pruner
        if D_wipe_out == True:
            return True, pruner
    else:
        for vals in newVar.cur_domain():
            #InitiatE Q with all constraints with regard to var
            #We prune all values of V != d from curDomain[V]
            newvarval = newVar.get_assigned_value()
            if vals != newvarval: ## Yeah its fine
                if (pruner.count((newVar, vals)) == 0): #Check if we have pruned it already
                    pruner.append((tuple((newVar, vals))))
                    newVar.prune_value(vals)
        #Do GAC enforce with constraints containing newVar on GAC Queue
        for con in csp.get_cons_with_var(newVar):
            #for each constraint C containing newVar put on GAC queue
            GAC_queue.enqueue(con)
        
        D_wipe_out, pruner = GAC_enforce(csp, GAC_queue, pruner)
        if D_wipe_out == True:
            return True, pruner
        if D_wipe_out == False:
            #Restore all values pruned from curdoms
            #We look at if there are values in our domain that are not in our current domain and unprune those
            #So we unprune values to current domain
            for i in newVar.domain():
                if newVar.cur_domain().count(i) == 0:
                    newVar.unprune_value(i)
            return False, pruner




