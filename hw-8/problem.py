from z3 import *  
from itertools import *  
  
# IO Pairs:  
  
#   OUT:  35840 IN: (11, 6, 9, 4)  
#   OUT:  46080 IN: (9, 12, 10, 1)  
#   OUT:     12 IN: (2, 4, 0, 4)  
#   OUT:  52224 IN: (14, 8, 10, 3)  
#   OUT:   6657 IN: (1, 13, 9, 4)  
#   OUT:   2048 IN: (4, 2, 8, 0)  
#   OUT:  57344 IN: (15, 6, 12, 4)  
#   OUT:   5376 IN: (7, 12, 6, 0)  
#   OUT:      0 IN: (2, 0, 6, 0)  
#   OUT:    520 IN: (16, 4, 3, 1)  
  
io_pairs = [ ((11, 6, 9, 4), 35840)  
           , ((9, 12, 10, 1), 46080)  
           , ((2, 4, 0, 4),   12)  
           , ((14, 8, 10, 3), 52224)  
           , ((1, 13, 9, 4), 6656)  
           , ((4, 2, 8, 0), 2048)  
           , ((15, 6, 12, 4), 57344)  
           , ((7, 12, 6, 0), 5376)  
           , ((2, 0, 6, 0), 0)  
           , ((16, 4, 3, 1), 520)  
           ]  
  
# Convenience functions for creating a constraint using a flag with identifier  
# 'i' that toggles whether the operator is used for operands x1 and x2.  
# Use is OPTIONAL.  
def mul(i,x1,x2): return (BitVec('B'+str(i),16) & 0x0001)*(x1 * x2)                   
def lor(i,x1,x2): return (BitVec('B'+str(i),16) & 0x0001)*(x1 | x2)                   
def shl(i,x1,x2): return (BitVec('B'+str(i),16) & 0x0001)*(x1 << x2)  
def add(i,x1,x2): return (BitVec('B'+str(i),16) & 0x0001)*(x1 + x2)  
  
# Your Synthesizer: construct a Z3 formula using input/output pairs.  
def formula(pairs):  
  return True  
  
def check(pairs):  
  # Once Z3 gives you a solution for the operators, check your answer on all  
  # inputs by changing the program function below.  A 'wrong' version adding  
  # all the inputs has been given as an example.  
  
  def program(a,b,c,d): return (a + b + c + d) & 0xFFFF # change the +'s to the correct operators  
  
  sat = True  
  for (a,b,c,d),o in pairs:  
    sat = sat and (program(a,b,c,d) == o & 0xFFFF)  
  
  if sat:  
    print 'Your program satisfies all IO pairs!'  
  else:  
    print 'Your program does not satisfy the IO pairs'  
  
if __name__ == '__main__':  
  
  s = formula(io_pairs)  
  print 'Z3 formula:',s  
  print 'Z3 Solution:'  
  solve(s)  
  
  check(io_pairs)  
