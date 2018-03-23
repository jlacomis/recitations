# Online Z3

Here is the solution using online Z3. It assumes we know the length is 5 (this is why finding the solution generally works better with a programmatic solution).
We restrict the char range to 'a'-'z', though multiple solutions exist in the '0-Z' range.

```smt
; This example illustrates basic arithmetic and 
; uninterpreted functions

(declare-const x0 (_ BitVec 32))
(declare-const x1 (_ BitVec 32))
(declare-const x2 (_ BitVec 32))
(declare-const x3 (_ BitVec 32))
(declare-const x4 (_ BitVec 32))

(assert (bvule x0 #x0000007a))
(assert (bvule x1 #x0000007a))
(assert (bvule x2 #x0000007a))
(assert (bvule x3 #x0000007a))
(assert (bvule x4 #x0000007a))

(assert (bvuge x0 #x00000061))
(assert (bvuge x1 #x00000061))
(assert (bvuge x2 #x00000061))
(assert (bvuge x3 #x00000061))
(assert (bvuge x4 #x00000061))

(assert 
  (=
    (bvand
      (bvadd (bvmul #x00000021
        (bvadd (bvmul #x00000021
          (bvadd (bvmul #x00000021
            (bvadd (bvmul #x00000021 
              (bvadd (bvmul #x00000021 #x00001505) x0)
            ) x1) 
          ) x2)
        ) x3)
      ) x4)
      #xffffffff)
    #x0f5c10af)
  )

(check-sat)
(get-model)
```

```smt
sat
(model 
  (define-fun x3 () (_ BitVec 32)
    #x00000065)
  (define-fun x2 () (_ BitVec 32)
    #x00000076)
  (define-fun x1 () (_ BitVec 32)
    #x00000065)
  (define-fun x4 () (_ BitVec 32)
    #x00000065)
  (define-fun x0 () (_ BitVec 32)
    #x00000065)
)
```

So `x0 = e`, `x1 = e`, `x2 = v`, `x3 = e`, `x4 = e`.

# Python solution

Build up the constraints with a loop. This tries a string of length 2, then 3, then 4, up to 10. A solution is found for n = 5.

```python
from z3 import *

for n in xrange(2, 10):

    vars = [BitVec('x'+str(i),32) for i in range(n)]

    constraints = []

    current = 0x1505 * 33 + vars[0]
    for i in xrange(1,n):
        current = (current * 33) + vars[i]
        constraints.append(current)

    last = ((constraints[-1] & 0xFFFFFFFF) == 0xf5c10af)
    constraint_vars = [And(ord('a') <= i, i <= ord('z')) for i in vars]

    constraint_vars.append(last)
    s = tuple(constraint_vars)

    print 'Constraints:',s
    solve(*s)
```
