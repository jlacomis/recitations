# Set up

Download z3 for your platform from the [releases](https://github.com/Z3Prover/z3/releases). Unzip it in a directory of your choosing. You may need 
to set up a library path so that you can use the Python API. For Linux, this is `export LD_LIBRARY_PATH=/path/to/z3/bin/` and Mac `Z3_LIBRARY_PATH=/path/to/z3/bin`. Check that it works by:

```
cd /path/to/z3/bin/python
python example.py
```

You should see 

```
sat
[y = 3/2, x = 4]
```

# Challenge

Here is some code that does a checksum over a string `s`:

```python
def checksum(s):                                                                    
  v = 0x1505                                                                        
  for i in xrange(len(s)):                                                          
    v = 33 * v + ord(s[i])                                                          
                                                                                    
  return v
  
FIND_THIS_STRING = "???"
checksum(FIND_THIS_STRING) & 0xFFFFFFF) == 0xf5c10af
```

Your job is to find a string `s` (using z3) that satisfies a checksum `0xf5c10af`. Specifically, your string should cause the following to be true:

`checksum(FIND_THIS_STRING) & 0xFFFFFFF) == 0xf5c10af`

**Don't brute force it, that will take too long.**

The set of possible characters is `0-9a-zA-Z`. I'm not telling you the length.

You can check for the right answer using the checksum code above. When you think you have it, submit it to the server which will check your answer.
You can talk to it like this:

```
nc clegoues-ubuntu-vm1.andrew.cmu.edu 7777
```

or with telnet (if you use windows):

```
telnet clegoues-ubuntu-vm1.andrew.cmu.edu 7777 
```

Note: Use __[bitvectors](https://rise4fun.com/z3/tutorialcontent/guide#h25)__ and not int variables; 
the latter may make life needlessly difficult. Use a bitvector length of 32. See below for example code...

## Python API

While you can solve this using the web interface, its highly recommended you use the python library which: (a) takes care of casting bitvectors to the right length and (b) lets you use
infix notation for arithmetic expressions.


You can declare bitvector variables in python like this:

```
my_bitvector_variable = BitVec('x1',32)
```

Here's a boilerplate code to get you started:

```python
from z3 import *

oracle = 0xf5c10af

x1 = BitVec('x1', 32)
x2 = BitVec('x2', 32)

constraints = []

constraint_x1 = x1 < 99
constraint_x2 = x2 > 20

constraints.append(constraint_x1)
constraints.append(constraint_x2)

# The above two lines is the same as using logical 'And' included in z3, used like this:
# constraints.append(And(constraint_x1, constraint_x2))

s = tuple(constraints)
print "Constraints: ",s

print "Solution?"
solve(*s)
```

If you have z3 set up correctly, you should see:

```
Constraints:  (x1 < 99, x2 > 20)
Solution?
[x2 = 21, x1 = 98]
```

## Hint

<details>
  <summary>Click to expand a hint</summary>
  
The idea is to build up constraints based on the checksum function. Let's pretend our string was simply "a". The checksum will calculate:
`v = 33 * 0x1505 + ord('a') = 177670 = 0x2b606`.

How about if our string was "ab"? The checksum will calculate:
`v = 33 * (33 * 0x1505 + ord('a')) + ord('b') = 0x597728`

And so on.

So `checksum` can be summarized by a bunch of constraints on some number of characters. We can express the constraints and use symbolic variables for the characters.
Here is a z3 example for the one character case, where we want to solve some character for the checksum `0x2b606`. Above, we know that "a" will work. Can z3 tell us this?

```
(declare-const x (_ BitVec 32))

(assert (= (bvadd (bvmul #x00000021 #x00001505) x) #x0002b606))

(check-sat)
(get-model)
(exit)
```

(Note that in online z3, the bitvector lengths must all be the same. One more reason to use the python API instead, which handles
this automatically for you!)

This gives the solution 

```
sat
(model 
  (define-fun x () (_ BitVec 32)
    #x00000061)
)
```

No surprise, `0x61` is the ascii character `'a'`. You can see this by printing `ord('a')` in python.

Here's a program that solves two characters for the checksum `0x597728`:

```
(declare-const x1 (_ BitVec 32))
(declare-const x2 (_ BitVec 32))

(assert (= (bvadd (bvmul #x00000021 (bvadd (bvmul #x00000021 #x00001505) x1)) x2) #x00597728))

(check-sat)
(get-model)
(exit)
```

Solution:

```
sat
(model 
  (define-fun x2 () (_ BitVec 32)
    #x00000000)
  (define-fun x1 () (_ BitVec 32)
    #xc1f07c83)
)
```

Oh! z3 gives us a strange solution. `x2` is `0x0` and `x1` is `0xc1f07c83`. While that satisfies the constraints, we can't represent `0xc1f07c83` in ascii.
Can we add more constraints to convince z3 to give us a reasonable solution?
</details>

## Hint 2

<details>
  <summary>Click to expand another hint</summary>
  
What if we tell z3 that the variables must be within ascii printable range? `z` is the value 122, or 0x7a. We can tell z3 that `x1` must be less than or equal to that:

`(assert (bvule x1 #x0000007a))`

(In python, we can simply add the constraint `constraint_x1 = x1 <= 0x7a`)

</details>



# References

- [Z3 online](https://rise4fun.com/Z3)
- [Z3 Guide](https://rise4fun.com/z3/tutorialcontent/guide#h23)
- [Python Z3 examples](http://ericpony.github.io/z3py-tutorial/guide-examples.htm)
- [Python API](http://z3prover.github.io/api/html/namespacez3py.html)

