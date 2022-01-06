# Conway's Soldiers/Leaping Frog game in Isabelle
This repository contains a formal proof in the Isabelle proof assistant about a game known as *Conway's Soldiers* or the *Leaping Frog game*.

The game consists of performing peg solitaire moves with coins placed on an infinite grid, with the goal of jumping 5 rows higher than where you started. John Conway showed that this is not possible, by an argument which involves the golden ratio in a very surprising way.

### The Leaping Frog game
Given is a rectangular grid and a horizontal line in the plane. In the beginning you may place an arbitrary amount of coins below the line. You can pick a coin and jump over an adjacent coin, removing the coin you jumped over.

```
|o|o|.| ⟶ |.|.|o|			Example of a jump
```

The goal is to repeatedly perform such jumps until you reach the fifth row above the line. However it turns out that it is not possible to reach the fifth row. The proof of this, due to John Conway, is based on the golden ratio φ. It uses the number ω = 1/φ = φ - 1 = (√5 - 1)/2, which satisfies the relation  ω² = 1 - 2.

The grid is modeled as the half-plane ℤ×ℕ, where the goal row on top is given y coordinate 0, and initially coins may be placed on all cells (x, y) with y ≥ 5. Each cell in the grid assigned a power of ω: Cell (x, y) is assigned ω^(x+y). To any coin configuration, we assign the sum of the cells it occupies.

The proof proceeds in three steps, which are possible because of properties of the number ω:
1. Show that the sum of all cell values where coins may be placed initially is equal to 1.
2. Show that any move can only decrease the sum of occupied cells, or leave it unchanged.
3. Observe that the goal field (0, 0) has value ω⁰. Show that therefore the goal field (0, 0) cannot be reached by a finite sequence  of moves.


### Formalization in Isabelle
I formalized the proof modeling
- coin configurations `coins` as sets of coin positions
- the valid game moves via a `jump` inductive predicate between coin configurations
- the sum of powers of ω via a `power_sum` function, which implements a double series

From this I showed four versions of the unwinnability theorem:
1. *From a finite set of initial coins, the goal field (0, 0) cannot be reached*
This is then strengthened in two ways:
2. *From a finite set of initial coins, no field (x, 0) on the goal row can be reached* (via a symmetry argument, involving shifting sequences of jumps to the right and left)
3. *From any (possibly infinite) set of initial coins, the goal field (0, 0) cannot be reached* (by showing that after any finite number of moves, some of the initial coins remain in place)
4. *From any (possibly infinite) set of initial coins, no field (x, 0) on the goal row can be reached* (by combining 2. and 3.)

Finally, I showed that the second-highest row *can* be reached by implementing an example of how to reach it.

### References
- E. Berlekamp, J. Conway and R. Guy, *Winning Ways for Your Mathematical Plays*
- Claudi Alsina and Roger B. Nelsen, *Charming Proofs: A Journey Into Elegant Mathematics*
- Miguel de Guzmán, https://www.oma.org.ar/red/la_rana.htm (online explanation of the proof	as performed here, in Spanish)

The game can be played here: https://www.cleverlearning.co.uk/blogs/blogConwayInteractive.php