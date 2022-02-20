#Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    csp, var_array = caged_csp_model(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the FunPuzz puzzle.

The grid-only models do not need to encode the cage constraints.

1. binary_ne_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only 
      binary not-equal constraints for both the row and column constraints.

2. nary_ad_grid (worth 10/100 marks)
    - A model of a FunPuzz grid (without cage constraints) built using only n-ary 
      all-different constraints for both the row and column constraints. 

3. caged_csp_model (worth 25/100 marks) 
    - A model built using your choice of (1) binary binary not-equal, or (2) 
      n-ary all-different constraints for the grid.
    - Together with FunPuzz cage constraints.

'''
from cspbase import *
import itertools


def binary_ne_grid(fpuzz_grid):
    n = fpuzz_grid[0][0] #Puzzle is nxn
    
    l = list(range(1, fpuzz_grid[0][0] + 1)) #1 - n
    #print(l)
    vars = []
    yc_matrix = []
    full_matrix = []
    long_list = []
    constraints_to_use = []
    r = [[0 for j in range(n)] for i in range(n)]
    constraint_list = []
    i = 0
    j = 0
    for column in range(n):
        yc_matrix = []
        for row in range(n):
            #make variables
            yc_matrix.append(Variable("(Q{},Q{})".format(row,column), l)) #Can take on these values in l (domain of the variable)
            long_list.append(yc_matrix[-1]) #Append from end just a list of everything
        full_matrix.append(yc_matrix) #[] just a matrix of columns first list, is first column
        for i in range(n):
            r[i][j] = yc_matrix[i] #Putting rows in so first list is the first row
        j += 1
    #Now we have all the variables assigned
    
    #So now we have a y matrix we can append all constraints to q1q1, then q2q1, q3q1
    binary_csp = CSP("binary_ne", long_list) #List of variables in the CSP (which is nxn matrix)

    for j in itertools.permutations(l, 2):
        constraint_list.append(j) #Will append tuples with everthing except (x, x)

    #Establish Constraints for our columns
    for column in full_matrix:
        for i in itertools.permutations(column, 2):
            #R1C1, R1C2,...  
            #Goes through tuples with unique values of Attributes
            #So it will start with comparing R1C1
            #We will create a constraint for the variable
            #So we create constraints for each pair of values
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]),[i[0], i[1]]) 
            #for j in itertools.permutations(l, 2):
            #    constraint_list.append(j) #Will append tuples with everthing except (x, x)
            con.add_satisfying_tuples(constraint_list)
            constraint_list = []
            binary_csp.add_constraint(con)
            #constraints_to_use.append(con)

    for row in r:
        for i in itertools.permutations(row, 2):
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]),[i[0], i[1]])
            con.add_satisfying_tuples(constraint_list)
            constraint_list = []
            binary_csp.add_constraint(con)
    
    return binary_csp, r

########################################################################3

def nary_ad_grid(fpuzz_grid):
    num = fpuzz_grid[0][0] #Puzzle is nxn
    l = []
    l = list(range(1, fpuzz_grid[0][0] + 1)) #1 - n
    yc_matrix = []
    full_matrix = []
    long_list = []
    constraints_to_use = []
    r = [[0 for j in range(num)] for i in range(num)]
    constraint_list = []
    i = 0
    j = 0
    for column in range(num):
        yc_matrix = []
        for row in range(num):
            #make variables
            yc_matrix.append(Variable("(Q{},Q{})".format(row,column), l)) #Can take on these values in l (domain of the variable)
            long_list.append(yc_matrix[-1]) #Append from end just a list of everything
        full_matrix.append(yc_matrix) #[] just a matrix of columns first list, is first column
        for i in range(num):
            r[i][j] = yc_matrix[i] #Putting rows in so first list is the first row
        j += 1
    #Now we have all the variables assigned

    #So now we have a y matrix we can append all constraints to q1q1, then q2q1, q3q1
    nary_csp = CSP("nary_ad_grid_csp", long_list) #List of variables in the CSP (which is nxn matrix)
    i = 0
    for j in itertools.permutations(l, num):
        constraint_list.append(j) #Will append tuples with everthing except (x, x) #Replace, never changes
    #Establish Constraints for our columns
    for column in full_matrix:
        for i in itertools.permutations(column, num):
            #R1C1, R1C2,...  
            #Goes through tuples with unique values of Attributes
            #So it will start with comparing R1C1
            #We will create a constraint for the variable
            #So we create constraints for each pair of values
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]), column) #Constrinat will be for n values so we will have to format that correctly :()
            con.add_satisfying_tuples(constraint_list)
            constraint_list = []
            #constraints_to_use.append(con)
            nary_csp.add_constraint(con)

    for row in r:
        for i in itertools.permutations(row, num):
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]), row)
            con.add_satisfying_tuples(constraint_list)
            constraint_list = []
            #constraints_to_use.append(con)
            nary_csp.add_constraint(con)
            
    for constrain in constraints_to_use:
        nary_csp.add_constraint(constrain)

    return nary_csp, r
    ##IMPLEMENT 
    
###################################################################################################################

def check_addition(tuple_list, requirment):
    sum = 0
    tuple_list_good = []
    for i in tuple_list: #List of possible values for say (x, y, z) which could be (1,2,4)
        for j in i:
            sum += j
        if (sum == requirment):
            tuple_list_good.append(i)
        sum = 0
    return tuple_list_good

def check_sub(tuple_list, requirment):
    sum = 0
    check_first = True
    tuple_list_good = []
    for i in tuple_list: #List of possible values for say (x, y, z) which could be (1,2,4)
        for j in i:
            if (check_first == True):
                sum = j
                check_first = False
            else:
                sum -= j
        if (sum == requirment):
            for b in itertools.permutations(i, len(i)):
                tuple_list_good.append(b)
        check_first = True
    return tuple_list_good

def check_div(tuple_list, requirment):
    sum = 0
    check_first = True
    tuple_list_good = []
    for i in tuple_list: #List of possible values for say (x, y, z) which could be (1,2,4)
        for j in i: #Checking each element of this tuple
            if (check_first == True):
                sum = j
                check_first = False
            else:
                sum = sum // j
        if (sum == requirment):
            for b in itertools.permutations(i, len(i)):
                tuple_list_good.append(b)
        check_first = True
        sum = 0
    return tuple_list_good

def check_mul(tuple_list, requirment):
    sum = 1
    tuple_list_good = []
    for i in tuple_list: #List of possible values for say (x, y, z) which could be (1,2,4)
        for j in i: #Checking each element of this tuple
            sum = sum * j  
        if (sum == requirment):
            tuple_list_good.append(i)
        sum = 1
    return tuple_list_good

def caged_csp_model(fpuzz_grid):
    ##IMPLEMENT 
    g = 1
    s = 1
    m = 1
    d = 1
    num = fpuzz_grid[0][0] #Puzzle is nxn
    l = []
    l = list(range(1, fpuzz_grid[0][0] + 1)) #1 - n
    y_matrix = []
    full_matrix = []
    long_list = []
    r = [[0 for j in range(num)] for i in range(num)]
    j = 0
    for column in range(num):
        y_matrix = []
        for row in range(num):
            #make variables
            y_matrix.append(Variable("(Q{},Q{})".format(row,column), l)) #Can take on these values in l (domain of the variable)
            long_list.append(y_matrix[-1]) #Append from end just a list of everything
        full_matrix.append(y_matrix) #[] just a matrix of columns first list, is first column
        for i in range(num):
            r[i][j] = y_matrix[i] #Putting rows in so first list is the first row
        j += 1

    caged_csp_model = CSP("caged_csp", long_list) #List of variables in the CSP (which is nxn matrix)
    for cage in fpuzz_grid[1:len(fpuzz_grid)]:
        if len(cage) == 2:
            #First element corresponds to the cell number
            #Second element coresponds to the value FORCED on that cell
            attribute = r[int(str(cage[0])[0])][int(str(cage[0])[1])]
            con = Constraint("C(Q{},Q{})".format(int(str(cage[0])[0]) - 1,int(str(cage[0])[1])- 1), [attribute])
            tu = (cage[1],)
            goose = []
            goose.append(tu)
            con.add_satisfying_tuples(goose)
            caged_csp_model.add_constraint(con)
        else:
            #Build list of impacted cells
            impact = []
            for i in range(0, len(cage) - 2):
                impact.append(r[int(str(cage[i])[0])-1][int(str(cage[i])[1])-1])
            requirment = cage[-2]
            #We should get a list of all the tuples possible for (len(cage) - 2) elements
            varDoms = [] #
            for v in impact:
                varDoms.append(v.domain()) 
            tuples = itertools.product(*varDoms)#We have combinations of the numbers provided in l with length of the amount of cells impacted
            tup = []
            for i in tuples:
                tup.append(i)
            if (cage[-1] == 0):
                con = Constraint("Addition Constraint #{}".format(g), impact) #Order matters btw
                g += 1
                #Check the addition and return the acceptable tuples
                con.add_satisfying_tuples(check_addition(tup, requirment))
                #constraint_list.append(con)
                caged_csp_model.add_constraint(con)

            if (cage[-1] == 1):
                #Check the subtraction
                con = Constraint("Subtraction Constraint #{}".format(s), impact) #Order matters btw
                s += 1
                #Check the addition and return the acceptable tuples
                con.add_satisfying_tuples(check_sub(tup, requirment))
                #constraint_list.append(con)
                caged_csp_model.add_constraint(con)

            if (cage[-1] == 2):
                #Check the division
                con = Constraint("Division Constraint #{}".format(d), impact) #Order matters btw
                d += 1
                #Check the addition and return the acceptable tuples
                con.add_satisfying_tuples(check_div(tup, requirment)) 
                caged_csp_model.add_constraint(con)
                #constraint_list.append(con)

            if (cage[-1] == 3):
                #Check multiplication
                con = Constraint("Multiplication Constraint #{}".format(m), impact) #Order matters btw
                m += 1
                #Check the addition and return the acceptable tuples
                t = check_mul(tup, requirment)
                con.add_satisfying_tuples(t) 
                caged_csp_model.add_constraint(con)
                #constraint_list.append(con)


    #So now we have a y matrix we can append all constraints to q1q1, then q2q1, q3q1
    #nary_csp = CSP("nary_ad_grid_csp", long_list) #List of variables in the CSP (which is nxn matrix)
    #use BNE stuff
    #Establish Constraints for our columns
    constrainty = []
    for column in full_matrix:
        for i in itertools.permutations(column, 2):
            #R1C1, R1C2,...  
            #Goes through tuples with unique values of Attributes
            #So it will start with comparing R1C1
            #We will create a constraint for the variable
            #So we create constraints for each pair of values
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]),[i[0], i[1]]) 
            for j in itertools.permutations(l, 2):
                constrainty.append(j) #Will append tuples with everthing except (x, x)
            con.add_satisfying_tuples(constrainty)
            constrainty = []
            #constraint_list.append(con)
            caged_csp_model.add_constraint(con)
            #constraints_to_use.append(con)

    for row in r:
        for i in itertools.permutations(row, 2):
            con = Constraint("C(Q{},Q{})".format(i[0],i[1]),[i[0], i[1]])
            for j in itertools.permutations(l,2):
                constrainty.append(j)
            con.add_satisfying_tuples(constrainty)
            constrainty = []
            #constraint_list.append(con)
            caged_csp_model.add_constraint(con)
            #constraints_to_use.append(con)

    return caged_csp_model, r