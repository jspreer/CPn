# for permutation iterators
import itertools

# for computing the inverse of a permutation
from sympy.combinatorics import Permutation

###############################################################################
###############################################################################
###############################################################################
# Helper functions
###############################################################################
###############################################################################
###############################################################################

def orderings(all_orderings,pos):
  '''
  This function produces all monotone paths defining the simplices in
  the canonical triangulation of the n-fold cartesian product of a triangle

  For a given n the function must be initiated with
  all_orderings = list of length 2n filled with '-1'
  pos           = 1

  output is a list of lists of length 2n filled with entries 1, ... , n
  length of list is (2n choose 2) x (2n-2 choose 2) x (4 choose 2)
  
  '''
  next_level = []
  # go through all partial paths found so far, and fill in the next value (pos)
  for lst in all_orderings:
    for i in range(len(lst)):
      # skip entries that are already filled
      if lst[i] != -1:
        continue
      # skip entries that are already filled
      for j in range(i+1,len(lst)):
        if lst[j] != -1:
          continue
        # fill every pair of unfilled entries with value 'pos'
        tmp = lst.copy()
        tmp[i] = pos
        tmp[j] = pos
        # add to new list of partial paths
        next_level.append(tmp)
  if not -1 in next_level[0]:
    # if done, return complete list of paths in cube
    return next_level
  else:
    # otherwise, call next level of recursion
    return orderings(next_level,3*pos)

def triangle_product(n):
  '''
  This function produces all simplices in the canonical triangulation of 
  the n-fold cartesian product of the triangle with vertices 0, .... , 3^n-1
 
  number of facets is the same as number of monotone paths returned by
  orderings(.,.) ((2n choose 2) x (2n-2 choose 2) x (4 choose 2) = 2n!/2^n)
  '''
  facets = []
  ords = orderings([[-1]*(2*n)],1)
  ords.sort()
  # turn paths into simplicial complex subdividing the n-fold cartesian product of the triangle
  for ordering in ords:
    f=[0]
    for k in ordering:
      f.append(f[-1]+k)
    facets.append(f)
  return facets
    
def boundary_faces(facets):
  '''
  This function returns the (Z2)-boundary of a simplicial complex defined by
  "facets"
  '''
  # record co-dim. one boundary faces of simplices as we see them
  faces = []
  # record their position as a pair [facet,boundary face index]
  pos = []
  for f in range(len(facets)):
    for k in range(len(facets[f])):
      tmp = facets[f].copy()
      tmp.remove(facets[f][k])
      if not tmp in faces:
        # add new boundary faces
        faces.append(tmp)
        pos.append([f,k])
      else:
        # remove boundary faces if we encounter them a second time
        pos.remove(pos[faces.index(tmp)])
        faces.remove(tmp)
  return faces,pos  
  
def faces_gem(facets):
  '''
  This function returns the gem defined by "facets", the simplicial subdivision
  of the n-fold Cartesian product of the triangle
  '''
  gem = []
  for i in range(len(facets[0])):
    gem.append([])
  # record co-dim. one boundary faces of simplices as we see them
  faces = []
  # record their position as a pair [facet,boundary face index]
  pos = []
  for f in range(len(facets)):
    for k in range(len(facets[f])):
      tmp = facets[f].copy()
      tmp.remove(facets[f][k])
      if not tmp in faces:
        # add new boundary faces
        faces.append(tmp)
        pos.append([f,k])
      else:
        # if we see face for second time, add dual edge to gem
        # check if faces are in same colour class (should always hold)
        old_idx = pos[faces.index(tmp)]
        if not k == old_idx[1]:
          return None
        gem[k].append([old_idx[0],f])
  return gem
    
def orbits(n):
  '''
  This function returns the set of orbits (each of length n!) of the natural
  Sym(n)-action on the coordinates of the n-fold cartesian product of
  the 2-triangle 2-sphere
  
  Idea is that an orbit is made out of all permutations of the letters of
  the defining orbit (on the level of a simplex in a cell), with
  target cell defined by permuting the letters of the cell label
 
  For this, we use the following global counting of simplices:
  1. triangulation of one cell has ordering of simplices i according
     to lexicographic ordering of path labels (N simplices overall)
  2. For cell B_j = {U,L}^n, we can number from all U = 0 to all L = 2^n-1
  3. Global index of simplex is then idx = i + N x j
 
  Orbits:
   (A) Every orbit must contain one representative of every permutation of paths
   (B) This gives groups of orbits of n! paths in {n choose #Us} = {n choose #Ls}
       facets
   (C) If a simplex is given by a path p in a cell c, then, for all sigma in
       Sym(n): produce sigma(p x c)
  
  Coordinate axes are encoded as follows:
   1        -> x_1
   3        -> x_2
   3^i      -> x_(i+1)
   3^(n-1)  -> x_n
  '''
  lut = [1]
  for k in range(1,n):
    lut.append(3*lut[-1])
  lut.reverse()
  # list for orbits (each entry of length n!, (2n)!/n! orbits)
  orbs = []
  # paths definining simplices and number of simplices in triangulation of cell
  paths = orderings([[-1]*(2*n)],1)
  paths.sort()
  cell_len = len(paths) # this is equal to int(math.factorial(2*n)/2**n)
  # for conversion of cell number to binary
  frmt = "0"+str(n)+"b"
  # symmetric group on n elements
  all_perms = list(itertools.permutations(list(range(n))))
  # loop over all cells c
  for c in range(2**n):
    # loop over all simplices in cell c
    for q in range(cell_len):
      # check if we have seen this facet already
      already_done = False
      for o in orbs:
        if cell_len*c + q in o:
          already_done = True
          break
      if already_done:
        continue
      # found a representative for an orbit not yet processed
      # convert cell number to binary
      bnr = format(c, frmt)
      # collect group of orbits (orbit in cell) x (orbit of cells)
      all_bnrs = list(set(list(itertools.permutations(list(bnr)))))
      all_bnrs.sort()
      for seed in all_bnrs:
        cur_orb = []
        # permute paths by all permutation on n letters
        for p in range(len(all_perms)):
          # variable for permuted path
          new_path = []
          for k in paths[q]:
            new_path.append(lut[all_perms[p][lut.index(k)]])
          # determine target cell (permute cell)
          new_seed = list(seed)
          # take inverse of permutation
          sigma = Permutation(list(all_perms[p]))**(-1)
          # binary word for cell is in reverse with respect to coordinate axes enumeration
          new_bnr = []         
          new_seed.reverse()
          for k in list(sigma):
            new_bnr.append(new_seed[k])
          new_bnr.reverse()
          # represent cell label as binary string for conversion
          P = ''.join(new_bnr)
          dec = int(P,2)
          # add new facet in target cell to orbit
          cur_orb.append(dec*cell_len+paths.index(new_path))
        cur_orb.sort()
        orbs.append(cur_orb)
  orbs.sort()
  return orbs
  
def simpToReg(simp,d,triangulation,perm):
  '''
  Turn facet list of simplicial complex into Regina triangulation
  
  Here, this is only applied to the simplicial subdivision of the n-fold cartesian
  product of a triangle (2 x n = d)
  
  simp          = facet list (of abstract simplicial complex)
  d             = dimension of triangulation (d = len(simp[0])-1)
  triangulation = appropriate regina function for generating a d-dimensional triangulation
  perm          = approoriate regina function for permuting elements of a simplex
                  (d+1) points
  '''
  facets = []
  for i in range(d+1):
    tmp = list(range(d+1))
    tmp.remove(i)
    facets.append(tmp)
  n = len(simp)
  neighbours = []
  gluings = []
  for j in range(n):
    neighbours.append([None] * (d+1))
    gluings.append([None] * (d+1))
    for f in range((d+1)):
      found = False
      for k in range(n):
        if k == j:
          continue
        good = True
        for i in range(d):
          if simp[j][facets[f][i]] not in simp[k]:
            good = False
            break
        if not good:
          continue
        found = True
        break
      if not found:
        continue
      neighbours[j][f] = k
      tmp = [None] * (d+1)
      unused = int(d*(d+1)/2)
      for i in range(d):
        adj = simp[k].index(simp[j][facets[f][i]])
        tmp[facets[f][i]] = adj
        unused = unused - adj
      tmp[f] = unused
      gluings[j][f] = perm(tmp)
  ans = triangulation()
  for j in range(n):
      ans.newSimplex()
  for j in range(n):
    for f in range(d+1):
      if ans.simplex(j).adjacentSimplex(f) == None and gluings[j][f] != None:
        ans.simplex(j).join(f,ans.simplex(neighbours[j][f]), gluings[j][f])
  return ans
  



