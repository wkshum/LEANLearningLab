## Boolean algebra

##### Symbols:
- *true*, *false*
- 1, $\top$ (top), 0, $\bot$ (bottom)
- variables $x$, $y$, ...

### Definition (Syntax of Boolean expressions)

$$ E ::= 1\, |\, 0\, |\, x \, |\, \neg E\, |\, E\wedge E\, |\,  E \vee E 
$$
- Atomic expression
	- $1$, $0$, $x$
- Compound expression
	- $x\vee y$, $x\wedge y$, $\neg x$ 

### Definition (Semantics of Boolean expressions)
 $$ \begin{align}
 E_1 \wedge E_2 &= \begin{cases} 
  1 & \text{if } E_1 = 1 \text{ and } E_2 = 1\\
  0& \text{otherwise} \end{cases}
 \\
   E_1 \vee E_2 &= \begin{cases} 
  1 & \text{if } E_1 = 1 \text{ or } E_2 = 1\\
  0& \text{otherwise} \end{cases} \\
   \neg E &= \begin{cases} 1 & \text{if } E=0  \\
0 & \text{if } E=1\end{cases} 
\end{align}   
$$

### Definition (Secondary operators)
$$\begin{align}
 x \rightarrow y &= (\neg x) \vee y \\
 x \oplus y & = (x \wedge (\neg y)) \vee ((\neg x) \wedge y) \\
 x \equiv y & = (x\wedge y) \vee ((\neg x) \wedge (\neg y))
\end{align}$$

### Definition (Binary relation)
- A **binary relation** $R$ between two sets $A$ and $B$ is a subset of 
$$\{(a,b):\, a\in A \text{ and } b\in B\}$$
* We say that "$a$ is related to $b$" if $(a,b)\in R$.
* We write $a R b$ if $a$ is related to $b$.

### Definition (Equivalence relation)
- A binary relation on $X$ is an **equivalence relation**  if it satisfies the following conditions:
1. (reflexivity) $x\sim x$ for all $x$ in $X$
2. (symmetry) if $x\sim y$ then $y\sim x$, for all $x, y \in X$
3. (transitive) if $x\sim y$ and $y\sim z$ then $x\in z$, for all $x,y,z \in X$

### Definition (Equality relation)
A binary relation is said to be an **equality relation** if it is an equivalence relation satisfying an additional condition:
4. (anti-symmetry)  if $x\sim y$ and $y\sim x$ then $x$ and $y$ are the same element in $X$.

This definition looks like a circular definition. It characterizes the meaning of "equality" as a relation.

### Laws of Boolean algebra
For $x$ and $y$ and $z$,
- Associativity of $\vee$:  $x\vee (y\vee z) = (x \vee y) \vee z$.
- Associativity of $\wedge$:  $x\wedge (y\wedge z) = (x \wedge y) \wedge z$.
- Commutativity of $\vee$: $x \vee y = y \vee x$.
- Commutativity of $\wedge$: $x \wedge y = y \wedge x$.
- Identity for $\vee$: $0 \vee x = x$. 
- Identity for $\wedge$: $1 \wedge x = x$.
- Annihilator for $\vee$: $1\vee x = 1$.
- Annihilator for $\wedge$: $0 \wedge x = 0$.
- Idempotent for $\vee$: $x\vee x = x$.
- Idempotent for $\wedge$: $x\wedge x = x$.
- Distributivity of $\vee$ over $\wedge$: $x \vee (y \wedge z) = (x\vee y) \wedge (x \vee z)$.
- Distributivity of $\wedge$ over $\vee$: $x \wedge (y\vee z) = (x\wedge y) \vee (x\wedge z)$.
- Absorption rule 1: $x \wedge (x \vee y) = x$.
- Absorption rule 2: $x\vee (x\wedge y) = x$.
- Complementation rule 1: $x \wedge (\neg x) = 0$.
- Complementation rule 2: $x \vee (\neg x) = 1$.
- Double negation : $\neg (\neg x) = x$.
- DeMorgan law 1: $\neg(x\vee y) = (\neg x) \wedge (\neg y)$.
- DeMorgan law 2: $\neg (x \wedge y) = (\neg x) \vee (\neg y)$.

### Truth table semantics
- If all the values in the column are 1s, the expression is said to be **valid**.
- If some of the values in the column are 1s, the expression is said to be **satisfiable**.
- If all of the values in the column are 1s, the expression is said to be **unsatisfiable**.

`x  y   x ∧ y  x ∧ y  x⊕y  x → y`

`0  0     0      0      0     1`

`0  1     0      1      1     0`

`1  0     0      1      1     1`

`1  1     1      1      0     1`







**Reference**
* Hou, Fundamentals of logic and computation, Chapter 1
