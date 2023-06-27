import itertools as it
from itertools import chain
from sage.combinat.shuffle import ShuffleProduct


s = SymmetricFunctions(QQ).schur()  #Schur basis for symmetric functions
p = SymmetricFunctions(QQ).p()      #Power-sum symmetric functions
m = SymmetricFunctions(QQ).m()

### Converting formal symbols (cells and permutations) to actual vectors and matrices:

def sign(s):                   #return the sign of the permutation (-1)^s
    return Permutation(s).sign()

def rho(s):    #return the matrix associated with a permutation of the configuration points: sign(s)*rho(s)^(-1)
    if len(s)<n:
        s.append(n)
    return rep.representation_matrix(Permutation(s).inverse())
#    s = Permutation(s) #convert to permutation
#    return s.sign()*rep.representation_matrix(s.inverse())    # instead we should/will conjugate partitions


def vector_form(pair): #convert a formal chain into an actual vector
    [cell,permutation] = pair
    permutation = list(permutation)
    #model a direct sum of N copies of a space of matrices by stacking them one on top of the other
    if cell[-1] == n:
        rows = topcells
    else: #cell[-1] == n-1
        rows = botcells

    mat = matrix(d*len(rows),d)      #matrix of zeros
    offset = rows.index(cell) #linearly order the cells, find position of current cell
    mat[d*offset: d*(offset+1)] = rho(permutation)    #insert "permutation" in the right place
    return mat

### Operations on cells: drop index (for differential), flips, swaps, left/right transvections, and the full cycle

def drop(k, cell):                    #dropping the k-th entry results in moving it to the last element
    new_cell = cell.copy()
    for j in range(1,len(cell)):
        if cell[j] >= k :
            new_cell[j] -= 1
    new_ordering = list(chain(range(1,k),range(k+1,cell[-1]+1), [k]))
    return vector_form( [new_cell, new_ordering] )

def swap(j,k,cell):    #realise the automorphism that swaps two degenral cells j and k.
    if j>k:
        [j,k] = [k,j]
    new_ordering = list(chain(range(1,cell[j-1]+1) , range(cell[k-1]+1,cell[k]+1), range(cell[j]+1,cell[k-1]+1), range(cell[j-1]+1,cell[j]+1) , range(cell[k]+1,cell[-1]+1)))
    new_cell = cell.copy()
    for i in range(j,k):
        new_cell[i] = cell[i]+cell[k]-cell[k-1]-cell[j]+cell[j-1]
    return vector_form( [new_cell, new_ordering] )

def cycle(cell, direction = 1):  #realize the automorphism that cycles all edges i_j -> i_{j+1}, the process proceeds by removing the last divider and adding a new first one
    if direction == 1:
        last = cell[-1] - cell[-2]  # number of points on the last arc, to be added to all other positions
        new_cell = list( vector(cell) + vector( [last]*len(cell) )  )   #adding the last arc to all arcs
        new_cell.pop()  #remove the last element, which is now (n + last), the new last element will now be n.
        new_cell = [0] + new_cell  #reintroduce the leading 0.
        new_ordering = list(chain(range(cell[-2]+1,cell[-1]+1), range(1, cell[-2]+1)))
        return vector_form( [new_cell, new_ordering] )
    else: #in the reverse direction (e_2|e_3|...|e_g|e_1)
        #the new cell is obtain by removing the points on the first arc from all later arcs
        new_cell = list( vector(cell) - vector( [cell[1]]*len(cell) )  )
        new_cell.pop(0) #remove 0th element, which is now -cell[1]
        new_cell += [cell[-1]]
        new_ordering = list(chain(range(cell[1]+1,cell[-1]+1), range(1, cell[1]+1)))
        return vector_form( [new_cell, new_ordering] )

def flip(j, cell):         #realize the automorphism that reverses the j-th edge. Here j can be 1,...,g
    # the new ordering is 1, ... i_{j-1} | i_j i_j-1 ... i_{j-1}+1 | i_j+1 ...
    new_ordering = list(chain(range(1,cell[j-1]+1) , range(cell[j],cell[j-1],-1) , range(cell[j]+1,cell[-1]+1) ))
    # the name of the cell remains the same, but orientation gets reversed depending on number of points on the arc
    return (-1)^(cell[j]-cell[j-1]) * vector_form( [cell, new_ordering] )

def flip_all(cell):         #realize the automorphism that reverses all edges.
    # the new ordering is ...| i_j i_j-1 ... i_{j-1}+1 | ... for all j
    new_ordering = list(chain(*[range(cell[j],cell[j-1],-1) for j in range(1,g+1)]))
    # the name of the cell remains the same, but orientation gets reversed depending on number of points on the arc
    return (-1)^cell[-1] * vector_form( [cell, new_ordering] )

def transvection_right(j,k,cell):    #realize the transvection automorphism: e_j -> e_j*e_k
    #so the points on (e_j) get distributed between (e_j) then (e_k)
    #split (e_j) into two batches of points. The 1st batch stays on (e_j) in order,
    #2nd batch gets shuffled in with the existing points on (e_k).

    #The sum of the resulting transformations gets added together into a single vector form.

    action = matrix(d* (len(topcells) if cell[-1]==n else len(botcells)) ,d)  #initialize zero vector form
    for l in range(cell[j-1],cell[j]+1): #ways to split the j-th edge (...|i_{j-1} ... l || l+1 ... i_j | ...)
        new_cell = cell.copy()
        ### Set up new dividers
        if j<k:
            # new cell has all dividers between j and k lowered by (i_j-l) steps; other dividers unchanged.
            for i in range(j,k):
                new_cell[i] -= cell[j]-l
            # shuffle the latter points from (e_j) into existing points on (e_k)
            for shuffle in ShuffleProduct(range(l+1,cell[j]+1),range(cell[k-1]+1,cell[k]+1)):
                new_ordering = list(chain( range(1,l+1), range(cell[j]+1,cell[k-1]+1) , shuffle, range(cell[k]+1,cell[-1]+1) ))
                #add resulting shuffled cell to the vector form
                action += vector_form( [ new_cell, new_ordering ] )

        else:
            # when k<j need to add (i_j-l) to all dividers between k and j
            for i in range(k,j):
                new_cell[i] += cell[j]-l
            # shuffle latter point from (e_j) into existing ones on (e_k)
            for shuffle in ShuffleProduct(range(l+1,cell[j]+1),range(cell[k-1]+1,cell[k]+1)):
                new_ordering = list(chain( range(1,cell[k-1]+1), shuffle, range(cell[k]+1, l+1), range(cell[j]+1,cell[-1]+1) ))
                #add resulting shuffled cell to the vector form
                action += vector_form( [ new_cell, new_ordering ] )

    return action


def transvection_left(j,k,cell): # similar to the right transvection above, but now e_j -> e_k*e_j.
    # The only difference is that now the 1st batch of points from (e_j) are shuffled into (e_k) instead of the 2nd. Otherwise, the same ideas apply.

    action = matrix(d* (len(topcells) if cell[-1]==n else len(botcells)) ,d)
    for l in range(cell[j-1],cell[j]+1):
        new_cell = cell.copy()     # the resulting cell has the j-th divider increase by l, and the k-th divider lowered by l.
        if j<k:
            for i in range(j,k):
                new_cell[i] -= l-cell[j-1]
            for shuffle in ShuffleProduct(range(cell[j-1]+1,l+1),range(cell[k-1]+1,cell[k]+1)):
                new_ordering =  list(chain( range(1,cell[j-1]+1), range(l+1,cell[k-1]+1) , shuffle, range(cell[k]+1,cell[-1]+1) ))
                action += vector_form( [ new_cell, new_ordering ] )

        else: # when k<j
            for i in range(k,j):
                new_cell[i] += l-cell[j-1]
            for shuffle in ShuffleProduct(range(cell[j-1]+1,l+1),range(cell[k-1]+1,cell[k]+1)):
                new_ordering = list(chain( range(1,cell[k-1]+1), shuffle, range(cell[k]+1, cell[j-1]+1), range(l+1,cell[-1]+1) ))
                action += vector_form( [ new_cell, new_ordering ] )

    return action

def diffl(cell): # the differential applied to a cell, given in vector form
    bdry = matrix(d*len(botcells),d) # initialize the zero vector form.
    for i in range(1,g+1):  #consider the i-th arc
        if cell[i] - cell[i-1] > 1:        #arcs with one point or less do not contribute to the boundary
            bdry += drop(cell[i],cell) - drop(cell[i-1]+1,cell) # differential for partition p
    return bdry

def aut_matrix(word, cells): # construct a chain operator corresponding to a word in Out(F_g)
    #Input: a list of generators with leading scalar factor.
    # lT = left transvection (takes arguments j,k such that e_j -> e_k*e_j)
    # rT = right transvection (takes arguments j,k such that e_j -> e_j*e_k)
    # F = flip (takes argument j)
    # F-all = flip all edges
    # S = swap (takes arguments j,k for transposition e_j <--> e_k)
    # C = cycle (no arguments, rotates the arcs e_j -> e_{j+1})
    # D = double (takes arguemnt j such that e_j is wrapped around itself twice)
    num_rows = d*len(cells)
    isom_mat = word[0]*matrix.identity(num_rows)
    for w in word[1:]:   # feed a list of lists, eg. [+1,["lT",1,2],["rT",1,3],["F",2],["F",3]] for complete graph K3
        w_action = matrix(num_rows,0)
        for cell in cells:
            if w[0] == "F":
                new_rel = flip(w[1],cell)
            elif w[0] == "F-all":
                new_rel = flip_all(cell)
            elif w[0] == "C":
                new_rel = cycle(cell)
            elif w[0] == "S":
                new_rel = swap(w[1],w[2],cell)
            elif w[0] == "rT":
                new_rel = transvection_right(w[1],w[2],cell)
            elif w[0] == "lT":
                new_rel = transvection_left(w[1],w[2],cell)
            elif w[0] == "D":
                new_rel = double(w[1],cell)

            w_action = w_action.augment(new_rel)  #calculation for partition p

        isom_mat = isom_mat * w_action #calculation for partition p

    return isom_mat
    # instead let us construct directly the aut_matrices for all needed operations, to avoid multiplying matrices


def conf_cohomology(num_points, codim = 2 ,partitions = [], Show_Progress = False):
    #Returns the character of isometry invariants of homology in codimension=*codim*, restricted to optional set of partitions
    #(default is all partitions and codimension 1)
    #Option to print out partial calculations as Schur functions - use to know which partitions are crashing.

    global n #number of points
    global g #genus
    global topcells
    global botcells
    global rep #current representation
    global d #dimension of current representation
    global self_conjugate

    n = num_points
    g = 3

    #a cell is indexed by 12...i_1 | i_1+1... i_2 | ... | i_{g-1}+1...n
    topcells = [list(chain([0],l,[n])) for l in it.combinations_with_replacement(range(0,n+1),g-1)]
    #a cell is indexed by 12...i_1 | i_1+1... i_2 | ... | i_{g-1}+1...n-1
    botcells = [list(chain([0],l,[n-1])) for l in it.combinations_with_replacement(range(0,n),g-1)]

    character = 0 # Frobenius characteristic, computed character of homology

    if len(partitions) == 0:
        partitions = Partitions(n).list()
    else:
        partitions = [Partition(p) for p in partitions]

    for p in partitions:                 #run over the partitions~irreducibles

        if Show_Progress:
            print("Calculating for partition", p, end=" ")

        rep = SymmetricGroupRepresentation(p.conjugate())   #make the Specht module associated with the partition - this assigns a matrix to every permutation
        d = rep(range(1,n+1)).ncols()           #dimension of the representation

        diff = matrix(d*len(botcells),0)     #start constructing relations matrix.
        #It starts with the differential, then continues with Id-isoms, so that kernel is top homology invariants (and coker is bottom homology coinvariants)

        # compute differential: start with matrix with 0 columns and later augment with all vector forms
        for cell in topcells:
            diff = diff.augment(diffl(cell))

        if codim == 0:
            compute_cohomology = top_cohomology
        elif codim == 2: 
            compute_cohomology = bot_cohomology
        else:
            print("Only implemented calculation for codim = 0 and 2")
            return

        character += compute_cohomology(diff,Show_Progress) * s(p)

    return character

def top_cohomology(diff,Show_Progress):

    #First compute the image of the edge-contraction differential from K4&Can to Goggles at the codimension 1 homology.
    #Since the codim 1 homology is a cokernel of "diff" + cokernel of the Goggles-coinvariants ideal, the edge-contraction differential is computed by the same differential on chains, then projected down to the cokernel.


# the pruned differential for the top dimension, as explain in Section 5 of the paper, is
# [ d | 1-s | 1-t | (1-e)(1+r) ]
# Spanning tree of K4 are the edges (12),(23),(34)
#   The loops generating pi_1 are the paths
#      a = 2432 (24 -> a)
#      b = 21432 (14 -> b)
#      c = 2132 (13 -> c)
# s = ( b(-c) , a(-c) , -c ) - this is the K4 automorphism (12) in Sym(4)
# t = ( -c(b) , b , a ) - this is the K4 automorphism (1234) in Sym(4)
# r = ( -a , -b , -c ) - lateral reflection of the can
# e = ( b , a , c ) - left swap of parallel pair in can
# In the differential the last term is (1-e)(1+r) = (1-r) - (e-er), 
#    both parenthesized expressions permute the cells in the same way, so each acts by a block diagonal matrix.
    
#Let us compute s = ( b(-c) , a(-c) , -c ):
    s = matrix(d*len(topcells),0)
    for cell in topcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n)
        #Split a and b into two parts each, then shuffle the latter parts into c in opposite order
        column = matrix(d*len(topcells),d)
        new_cell = cell.copy()


        #TESTING:
#        old_ordering = range(1,n+1)
#        print("Old cell:", old_ordering[:cell[1]],'|' ,  old_ordering[cell[1]:cell[2]],'|' , old_ordering[cell[2]:])


        for k in range(cell[0],cell[1]+1): #splitting the first cell into [1,...,k|k+1,...,cell[1]]
            for j in range(cell[1],cell[2]+1): #splitting the second cell into [cell[1]+1,...,j|j+1,...,cell[1]]
                new_cell[1] = j - cell[1]
                new_cell[2] = k + j - cell[1]
                for shuffle_ab in ShuffleProduct(range(cell[1],k,-1), range(cell[2],j,-1)):
                    for shuffle_abc in ShuffleProduct(shuffle_ab, range(n,cell[2],-1) ): # Shuffling three things together = shuffle the third into the shuffles of the first two
                        new_ordering = chain(range(cell[1]+1,j+1), range(1,k+1) , shuffle_abc )
                        
                        #TESTING:
#                        new_ordering = list(new_ordering)
#                        print("New cells:")
#                        print( (-1)^(n-k-j + cell[1]) , "*", new_ordering[:new_cell[1]],'|' ,  new_ordering[new_cell[1]:new_cell[2]],'|' , new_ordering[new_cell[2]:])
                        
                        column += (-1)^(new_cell[3]-new_cell[2]) * vector_form( [new_cell,new_ordering]) # additional sign (-1)^(# pts on c) since points are moving backwards
        s = s.augment(column)

#Let us compute t = ( -c(b) , b , a ):
    t = matrix(d*len(topcells),0)
    for cell in topcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n)
        column = matrix(d*len(topcells),d)
        new_cell = cell.copy()
        new_cell[1] = n-cell[2] # number of points in a is what used to be the points in c
        for k in range(0,cell[1]+1): # Split a into two parts, second part shuffled into b, first taken as c in opposite direction
            new_cell[2] = n-k # number of points in c is the 1st part of a
            for shuffle in ShuffleProduct(range(k+1,cell[1]+1), range(cell[1]+1,cell[2]+1)): #then shuffle 2nd part of a with existing b,
                new_ordering = chain(range(cell[2]+1,n+1) , shuffle, range(k,0,-1) )
                column += (-1)^k * vector_form( [new_cell,new_ordering]) # additional sign (-1)^k since have k points moving backwards
        t = t.augment(column)

#Let us compute r = ( -a , -b , -c ): this is computed by the function "flip_all"
    r = matrix(d*len(topcells),0)
    for cell in topcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n-1)
        r = r.augment(flip_all(cell))

#Let us compute = ( b , a , c ): this is computed by the function "swap(1,2, cell)"
    e = matrix(d*len(topcells),0)
    for cell in topcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n-1)
        e = e.augment(swap(1,2,cell))

#Let us also compute er = ( -b , -a , -c):
    er = matrix(d*len(topcells),0)
    for cell in topcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n-1)
        new_cell = cell.copy()
        new_cell[1] = cell[2]-cell[1]
        new_ordering = chain(range(cell[2],cell[1],-1), range(cell[1],0,-1), range(n,cell[2],-1))
        er = er.augment(vector_form( [new_cell, new_ordering] ))
    er = (-1)^n * er #overall global sign, since all n points are moving backwards --- THIS LINE WAS PREVIOUSLY INDENTED(!)

    rk = block_matrix([[diff] , [1-s], [1-t], [1+r-e-er]]).rank()
#    rk = block_matrix([[diff] , [1-s], [1-t], [1-e]]).rank()


    if Show_Progress:
        print( "........ done!")
        print("In top homology found multiplicity:", d*len(topcells) - rk)
        print("------")

    return d*len(topcells) - rk

def bot_cohomology(diff, Show_Progress):
    cells = botcells
        
        #Construct operation V_{n-1}^{Aut(Gog)} --> V_n + V_{n-1} + V_{n-1}
        # given by [ d                                      ]   whose kernel we wish to compute
        #          | 1+swap(12)                             |   -- kernel computes he Aut(Gog)-invariants
        #          | 1-swap(14)swap(23)                     |
        #          | 1-Flip                                 |   -- differential Gog --> Can
        #          [ 1+c+c^2+c^3+sc+csc = (1+c)(1+(s+c)c)   ]   -- differential Gog --> K4
        # where the first two operators perscribe the Aut(Gog)-invariants, and defined by their action on
        #       the edges of the Banana graph with marking: a(  b(  c)  ) = 1(  2(  3)  4)
        # the kernel of this stacked matrix is the intersection of all respective kernels, and is the cycles of the double complex.

        # 1) swap(12) = (b,a,c) acts by odd permutation of edges, so acts with additional sign from det(Edges)
        # 2) swap(14)(23) = ( -a , c(-a) , b(-a) ) = swap_K4(34)
        # 3) Flip = ( -a , -b , -c )   - induces odd permutation of edges on Can graph, so acts with additional sign
        # 4) Cycle = the 4-cycle of the K4, computed as in "top_cohomology" above = ( -c(b) , b , a )
        # 5) swap_K4(12) = ( b(-c) , a(-c) , -c )
        #       To avoid computing the last complicated operator, observe that it is the conjugation of swap(14)(23) by (c,b,a).

        # relationship to operators in top_cohomology: cycle = t; swap_K4(12) = s; Flip = r; swap(12) = e; swap(14)(23)=swap_k4(34) = h;
        # last line of matrix: 1+t+t^2+t^3+st+tst OR 1+t+t^2+t^3+ht+tht = (1+t)(1+(h+t)t)
        # block matrix [ diff, 1+e, 1-h, 1-r, (1+t)(1+(h+t)t) ]

        # To compute cohomology of V_{n-1}^{Aut(Gog)} we only need to subtract the dimension of V_{n-1}^{Aut(Banana)}, 
        #    a group generated by two elements: (Flip)x(123) and (34).
        # 6) (Flip)xcycle(123) = (-b,-c,-a).
        # 7) swap(34) = ( a(-c) , b(-c) , (-c) )  - which is obtained from swap_K4(12) by pre/post composition with (b,a,c)=swap(12).
        # 7')swap(14) = swap(14)(23) * swap(23), but swap(23) is easy to calculate (a,c,b).


    #Start by computing e = swap(12): (a,b,c) --> (b,a,c)
    e = matrix(d*len(botcells),0)
    for cell in cells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n-1)
        e = e.augment( swap(1,2,cell) )


    #Next compute the operation r = Flip
    #        We can either compute Flip123^3 or this matrix. If matrix power is faster than computing "flip_all", we can choose that instead.
    r = matrix(d*len(botcells),0)
    for cell in cells: #cells have form          (12...i_1|i_1+1...i_2|i_2+1...n-1)
        r = r.augment(flip_all(cell))

    #Next compute the operation h = swap(14)swap(23): (a,b,c) --> ( -a , c(-a) , b(-a) )
    # b and c get split into two parts, and the latter half gets shuffles into a in reverse order
    h = matrix(d*len(botcells),0)
    for cell in cells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n)
        column = matrix(d*len(botcells),d)
        new_cell = cell.copy()

        for k in range(cell[1],cell[2]+1): #splitting the 2nd edge into [cell[1],...,k|k+1,...,cell[2]]
            for j in range(cell[2],cell[3]+1): #splitting the 3rd edge into [cell[2]+1,...,j|j+1,...,cell[3]]
                new_cell[1] = cell[1] + cell[2]-k + cell[3]-j
                new_cell[2] = cell[3] - (k - cell[1])
                for shuffle_ab in ShuffleProduct(range(cell[1],cell[0],-1), range(cell[2],k,-1)):
                    for shuffle_abc in ShuffleProduct(shuffle_ab, range(cell[3],j,-1) ): # Shuffling three things together = shuffle the third into the shuffles of the first two
                        new_ordering = chain( shuffle_abc, range(cell[2]+1,j+1) , range(cell[1]+1,k+1) )

                        column += (-1)^(new_cell[1]) * vector_form( [new_cell,new_ordering])
                                             #additional sign (-1)^(pts on new 'a') since points are moving backwards
        h = h.augment(column)

    #Make the t = Cycle (1234) on K4: ( -c(b) , b , a )
    t = matrix(d*len(botcells),0)
    for cell in botcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n)
        column = matrix(d*len(botcells),d)
        new_cell = cell.copy()
        new_cell[1] = cell[3]-cell[2] # number of points in a is what used to be the points in c
        for k in range(0,cell[1]+1): # Split a into two parts, second part shuffled into b, first taken as c in opposite direction
            new_cell[2] = cell[3]-k # number of points in c is the 1st part of a
            for shuffle in ShuffleProduct(range(k+1,cell[1]+1), range(cell[1]+1,cell[2]+1)): #then shuffle 2nd part of a with existing b,
                new_ordering = chain(range(cell[2]+1,cell[3]+1) , shuffle, range(k,0,-1) )
                column += (-1)^k * vector_form( [new_cell,new_ordering]) # additional sign (-1)^k since have k points moving backwards
        t = t.augment(column)

    #Make the swap12K4 by conjugation: (cba)^{-1}*swap12*(cba) - and bca has order 2
    # so first we make the conjugating matrix
        #    cba = matrix(d*len(botcells),0)
        #    for cell in botcells:
        #        cba = cba.augment(swap(1,3,cell))
        #    swap12K4 = cba*swap12*cba

    #For the image of the d_1-differential need to compute Flip*(123): (a,b,c) --> (-b,-c,-a)
    Flip123 = matrix(d*len(botcells),0)
    for cell in botcells: #cells have form (12...i_1|i_1+1...i_2|i_2+1...n-1)
        new_cell = [0, cell[3]-cell[2], cell[3]-cell[2]+cell[1] , cell[3] ]
        new_ordering = chain( range(cell[3],cell[2],-1), range(cell[1],0,-1), range(cell[2],cell[1],-1) )
        # new_cell = [0, cell[2]-cell[1], cell[3]-cell[1] , cell[3] ] # inverse
        # new_ordering = chain( range(cell[2],cell[1],-1) , range(cell[3],cell[2],-1) , range(cell[1],0,-1)) # inverse
        Flip123 = Flip123.augment( vector_form([ new_cell , new_ordering ]) )
    Flip123 = (-1)^(cell[3])* Flip123 #overall sign due to all n-1 points going in opposite direction

    # Swap(34) on Banana is given by swap12K4 * swap12
    #    swap34 = swap12K4 * swap12

    acb = matrix(d*len(botcells),0)
    for cell in botcells:
        acb = acb.augment(swap(2,3,cell))
    swap14 = acb*h

    diff_Gog = d*len(botcells) - block_matrix( [[ diff, 1+e , 1-h, 1-r , (1+t*(h+t))*(1+t)]] ).rank()
    diff_Ban = d*len(botcells) - block_matrix( [[ diff, 1-Flip123 , 1+swap14]] ).rank()
    #diff_Gog = d*len(botcells) - block_matrix( [[ diff , 1+e , 1-h , 1-Flip123^3 , (1+t)*(1+(h+t)*t) ]] ).rank()
    #diff_Ban = d*len(botcells) - block_matrix( [[ diff , 1-Flip123 , 1+swap14 ]] ).rank()

    if Show_Progress:
        print(" ... done!")
        print("dim Ker(diffGog) = ", diff_Gog)
        print("dim Ker(diffBanana) = ", diff_Ban)
        #FOR TESTING:
        print("Out of total dimension ",d*len(botcells))
    return diff_Gog - diff_Ban

# helper function
def dPart(F, d):
    R.<p1,p2,p3,p4,p6> = QQ[]
    F = F.polynomial(QQ)
    return sum( [ F.monomial_coefficient(m) * m for m in F.monomials() if  m.weighted_degree({p1:1, p2:2, p3:3, p4:4, p6:6}) == d ] )

# gives the degree n part of z_3 in terms of power sums
def z3(n):
    var('p1,p2,p3,p4,p6')
    faber_3 = -(1+p1)^4/(24*(1+p2)^3) + (1+p1)^2/(4*(1+p2)^2)+(1+p1)/(2*(1+p3))+(1+p3)*(1+p1)/(6*(1+p6))-1/(8*(1+p2))+(1+p2)/(4*(1+p4))
    taylor_series = taylor(faber_3, (p1, 0),(p2,0),(p3,0),(p4,0),(p6,0), n)
    expanded = taylor_series.expand()
    homogeneous = dPart(expanded, n)
    if homogeneous == 0:
        return 0
    else:
        symFnLookup = {'p1':p([1]), 'p2':p([2]),'p3':p([3]),'p4':p([4]),'p6':p([6])}
        symFnDic = {'{}'.format(ar): symFnLookup['{}'.format(ar)] for ar in homogeneous.args()}
        powerSum = homogeneous(**symFnDic)
        return powerSum

n=9
print("For n=",n)
char = conf_cohomology(n,codim = 0, Show_Progress = True)
#char = conf_cohomology(n,codim = 0, partitions = [[n],[1]*(n)], Show_Progress = True)
#char = conf_cohomology(n,codim = 2, partitions = [[n],[1]*(n)], Show_Progress = True)
print("Top cohomology character: ",char)
m = SymmetricFunctions(QQ).m()
print("Total dimension:",m(char).coefficient([1]*n))

char = conf_cohomology(n,codim = 2, Show_Progress = True)
print("Bottom cohomology character: ",char)
m = SymmetricFunctions(QQ).m()
print("Total dimension:",m(char).coefficient([1]*n))