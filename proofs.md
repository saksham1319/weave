# Proofs
> The impossibility results, theorems and corollaries behind [the certificate scheme](./mwac.v2.md), plus the pitfalls this repo hit on the way. `mwac.v2.md` stays readable; the math lives here.
>
> Each result carries a tag:
> - **[Lean: `Name`]** — formal statement in [`lean/`](./lean/README.md) (status: written offline, not yet machine-checked);
> - **[cited]** — a published result we rely on;
> - **[argument]** — a proof given here in prose.

## Conventions
- **Circumference.** $P$ is the circumference in blocks (blocks per ring). Lateral positions are counted in half-block units, so the ring is $W = 2P$ units round.
- **Planar coordinates.** A block is $v=(x,t)$ with $x+t$ even; layers $t$ grow downward.
  - Parents: $p_L(v)=(x-1,t-1)$ and $p_R(v)=(x+1,t-1)$.
  - **Meet** (the shared parent of the two parents): $q(v)=(x,t-2)$.
- **Light-cone coordinates.** $a=\tfrac{x+t}{2}$ and $b=\tfrac{x-t}{2}$, so $t=a-b$ and $x=a+b$.
  - $a \bmod P$ names the block's **left strand** and $b \bmod P$ its **right strand**.
  - A block is the crossing of its two strands.
- **Cone.** $\mathrm{cone}(v)$ is the closed past cone: $v$ plus every ancestor, i.e. all $u$ with $t_u\le t_v$ and $|x_u-x_v|\le t_v-t_u$.
- **Exclusive.** A state is *exclusive* when every coin has multiplicity 0 or 1.

---

## 1. Historical pitfalls
What this repo tried, why each attempt fails, and what replaced it.

### H1. Summing coin points over one generator
*v1 exclusivity certificate:* $(\sum_{I} C_i,\ \sum_{O} C'_i)$ with $C=rG$.

All coins are multiples of one public generator, so a sum is a single scalar times $G$.
- $\{aG,bG\}$ and $\{(a+b)G\}$ have equal sums but different sizes. Anyone who knows $a$ can split a coin into several that sum to it, which inflates supply.
- $\{C_A,C_A\}$ (a double spend) and $\{C_X,C_Y\}$ with $C_X+C_Y=2C_A$ have equal sums. The double spend is invisible.

**[Lean: `Weave.Pitfalls.sum_hides_cardinality`, `sum_hides_double_spend`]**

*Replaced by:* coins as slots (T1–T3).

### H2. Percolating with weight $n^{-1}$
*v1 index.md:* each parent scales its certificate by $1/n$ for its $n$ children, and a child sums its parents.

Unrolling the rule, an ancestor $k$ layers up at lateral offset $j$ is weighted $\binom{k}{(k+j)/2}/2^k$ instead of $1$. The meet ($k=2$, $j=0$) gets $\tfrac12$.

A coin created at $(x-1,t-3)$ and spent at $q(v)$ leaves residue $\tfrac38-\tfrac12=-\tfrac18$ in $v$'s certificate. So no single block's certificate is a digest of an integer multiset, and cut-through fails. The rule conserves mass only summed over a *whole ring*, which no partial node sees.

**[Lean: `Weave.Pitfalls.w`, `w_meet`, `w_far`, `percolation_residue`, `percolation_not_multiset`]**

*Replaced by:* handing certificates down, never summing (mwac.v2.md § Exclusivity certificate).

### H3. Summing parents' digests
Summing the two parents counts their shared history twice. The exact recurrence is inclusion–exclusion over the quad face:
$$D(v)=\Delta(v)+D(p_L)+D(p_R)-D(q(v))$$
This holds because the two parents' cones overlap in exactly the meet's cone (T4).

It is exact only less than half a lap deep. Past that, the cones also overlap round the back of the cylinder (T6). And even when exact, it certifies nothing about exclusivity (I1).

**[Lean: `Weave.Lattice.digest_recurrence`, `digest_recurrence'`]**

### H4. KZG over characteristic polynomials
Committing to $\prod(X-x_i)$ merges by polynomial *multiplication*. Multiplying committed polynomials takes a pairing, which gives one level only, so merge depth is bounded.

Hash-to-scalar roots fail separately: the committed values bind to hashes, not to the coins as points, so their sums say nothing about the coins. **[argument]**

### H5. LWE points with "error ≈ 0"
Each merge adds the errors, so after about $q/(4B)$ merges the check is meaningless; depth is bounded. The adversary also chooses its own errors, so this is not a proof of anything about honest construction. **[argument]**

### H6. "Two valid certificates merge into a valid one"
*v2's original interface requirement.* This is impossible for exclusivity: see **I1**.

*Replaced by:* merging conditioned on the adjacency and crossing checks (T7).

### H7. KZG slot tables (v3 "Variant K")
Constant-cost slot edits, but they bring a trusted setup and pairings, and wallets must keep their openings fresh.

Merkle trees cost $O(D)$ per edit, and $D$ is *fixed* because elasticity adds strands instead of deepening them. So Merkle cost is constant too, transparent, and optimal among hash-based options (I4). **[argument]**

### H8. Plain Nova for the DAG
Nova folds two instances at a time. A block with 3 parents would chain 5 folds, and Nova carries an error vector, which doubles the hand-off.

HyperNova folds all parents in one multi-fold via sum-check and has no error vector. **[argument]**

### H9. Draining a strand before retiring it
Moving $2^{D}$ coins at $K_c$ per block takes about $2^{D}/K_c$ layers, which is far too slow to be the contraction mechanism.

*Replaced by:* adoption. The sink's child takes the retiring trees whole, at constant cost, and counts carry over. **[Lean: `Weave.Slots.adopt_conserves`]**

### H10. Truncated strand ids as register keys
Keying meeting registers by a *truncated* hash lets a miner grind a new strand's id to collide with an existing one. Two strands then share a register entry and the crossing check can be dodged.

*Replaced by:* full-width ids (the hash of the birth block) in an indexed Merkle tree. **[argument]**

### H11. Elasticity trigger direction
`index.md` originally read "expand when timestamps drift apart". With fixed difficulty, *more* hash power means blocks arrive *faster*, so expansion must trigger when blocks beat the target time. Resolved in mwac.v2.md § Elasticity. **[argument]**

---

## 2. Impossibility results
These force the construction's shape. Each consequence names what the construction does about it.

### I1. Exclusivity is not closed under merging
**Statement.** No verifier can be all three of:
- **sound**: accepts only exclusive states;
- **complete**: accepts every exclusive state;
- **merge-closed**: accepts $q+t_1+t_2$ whenever it accepts $q$, $q+t_1$ and $q+t_2$ and both transactions conserve count.

**Proof.**
1. Let $q$ hold coin $x$. Let $t_1$ spend $x$ and create $y$, and $t_2$ spend $x$ and create $z$.
2. All three states are exclusive, and both transactions conserve count.
3. The merge has $x$ at multiplicity $-1$, so it is not exclusive.
4. Merge-closure would force the verifier to accept it, which contradicts soundness. ∎

**[Lean: `Weave.Merge.no_merge_closed_verifier`]**

**Consequence.** Merging *must* depend on something beyond the two certificates: that both branches share one history. The adjacency and crossing checks supply this (T7).

### I2. Signed cardinality is not supply
In I1's merged state the signed count is unchanged, but the number of spendable coins ($\sum_x\max(m_x,0)$) has grown by one.

$\max(\cdot,0)$ is not additive, so **no additive (homomorphic) digest can track spendable supply**.

**[Lean: `Weave.Merge.signed_conserved`, `spendable_grows`, `spendable_not_additive`]**

**Consequence.** Certify *exclusivity*. Scarcity then follows from per-transaction balance (T3). A separate scarcity certificate is redundant.

### I3. Binding is not well-formedness
- **Collisions exist.** Any digest that compresses must collide (pigeonhole), so binding can only ever be computational. **[Lean: `Weave.Digest.compressing_digest_collides`]**
- **The existence statement is empty.** In a group, every value is the sum of a multiset of every size $\ge1$. So "$\exists M:\ D(M)=d \wedge |M|=n$" is always true and says nothing. **[Lean: `Weave.Digest.every_digest_has_every_size`]**
- **What well-formedness must mean.** It has to be "*a valid history producing this certificate is known*". A fixed-size certificate for that is a succinct non-interactive argument for an NP statement with unbounded witness.
- **Gentry–Wichs.** By Gentry–Wichs (STOC'11), the adaptive soundness of such an argument cannot be proven from falsifiable assumptions via black-box reductions. **[cited]**

**Consequence.** Proof-carrying data (PCD) secured in the random-oracle or arithmetized-random-oracle model, or by knowledge assumptions, is necessary, not a convenience. Incremental constant work per block further forces the certificate to *be* PCD.

### I4. Hash-based dynamic sets cost $\Omega(\log n)$
Any hash-based authenticated dictionary of size $n$ has $\Omega(\log n)$ worst-case update and proof cost (Tamassia–Triandopoulos, ICALP'05). **[cited]**

**Consequence.** A per-edit cost of $D=\log_2(\text{slots per strand})$ is optimal for a transparent scheme. Because $D$ is fixed and elasticity adds strands instead, the cost is constant over the chain's life.

### I5. Recursion puts Fiat–Shamir inside the circuit
- Recursive folding must evaluate its Fiat–Shamir hash *inside* the circuit, which random-oracle proofs do not cover.
- Khovratovich–Rothblum–Soukhanov (ePrint 2025/118) break a real GKR-based argument when the attacker chooses a circuit that evaluates the hash. **[cited]**
- PCD does have a formal security model for arbitrary depth: the arithmetized random oracle model (Chen–Chiesa–Gur–O'Connor–Spooner, EUROCRYPT'23). **[cited]**

**Consequence.** Folding-based PCD at chain depth is secure under a heuristic, assumption A1 below. The fixed circuit, with its digest hashed into every transcript, is the known mitigation.

### I6. Quantum adversaries
Discrete-log folding (Pedersen commitments on Pasta) and Schnorr both fall to Shor's algorithm. **[cited]**

**Consequence.** The Merkle certificates are hash-based and survive. The folding layer and the signatures must be swapped for post-quantum ones (e.g. WARP, LatticeFold+, Neo, and a PQ signature).

---

## 3. Theorems for the construction

### T1. The edit equation
Rewriting one slot changes the count by exactly what was written minus what was there:
$$\mathrm{count}(t[i\mapsto v]) + \mathrm{occ}(t_i) = \mathrm{count}(t) + \mathrm{occ}(v)$$
**[Lean: `Weave.Slots.count_update`]**

### T2. Exclusivity is preserved, and double spends are impossible
- Spending an occupied slot keeps the table exclusive.
- Creating a fresh coin in an empty slot keeps it exclusive.
- Relocating (spend then create elsewhere, owner unchanged) keeps it exclusive.
- So does any valid run of such edits.
- After a coin is spent, no slot holds it, so a second spend has nothing to open.

**[Lean: `Weave.Slots.excl_spend`, `excl_create`, `excl_relocate`, `excl_run`, `no_double_spend`]**

### T3. Scarcity
- **Per run.** Over any valid run of edits, the count moves by the sum of the edits' deltas: $-1$ per spend, $+1$ per create. A balanced transaction ($|I|=|O|$) leaves it unchanged. A relocate changes nothing.
- **Per block.** A block's two strands form one table, whose count is the sum of the two strands' counts.

**[Lean: `Weave.Slots.count_run`, `count_relocate`, `count_pair`]**

**Corollary (Kirchhoff).** Summing T3 over any downward-closed region of blocks cancels every internal hand-off. So **the strand counts crossing any full ring sum to the total minted above it**.

### T4. The quad lemma
- **Intersection.** The two parents' cones overlap in exactly the meet's cone.
- **Union.** A block's cone is itself plus its parents' cones.
- The finite (down-to-genesis) versions of both also hold.

**[Lean: `Weave.Lattice.cone_inter`, `cone_union`, `cone_inter_finset`, `cone_eq_insert`]**

### T5. Case A: same-sheet merges are covered by the adjacency check
If both children of a block $u$ lie in $v$'s cone on the plane, so does their common child $m$. That common child's adjacency check compares the two references to $u$.

**[Lean: `Weave.Lattice.children_in_cone_meet_in_cone`]**

### T6. Case B: wrapping round takes at least half a lap
Lift the cylinder to the plane, so a block is identified with its copies shifted by multiples of $W$. Suppose $u$'s two children are reached in $v$'s cone through *different* windings. Then the cone is at least $W/2-1=P-1$ layers deep at the children.

Equivalently, below that depth both children come through the same winding, and T5 applies.

**[Lean: `Weave.Lattice.wrap_needs_half_lap`, `same_winding_below_half_lap`]**

### T7. Cone consistency
**Statement.** If every block in $\mathrm{cone}(v)$ passes the adjacency check and the crossing check, then $\mathrm{cone}(v)$ contains no two distinct blocks at the same position.

**Proof. [argument, geometric steps in Lean]**
1. Suppose not. Take an equivocating pair $u_1\ne u_2$ at the latest possible position $u$, so every position below $u$ holds a unique block.
2. Parent references are part of each block's hashed header. So $u_1$ and $u_2$ are referenced by the unique blocks at $u$'s two *different* child positions $c_1,c_2$; one block referencing both would be a hash collision.
3. **Same winding.** By T5, the common child $m$ is in the cone, and $m$'s adjacency check forces $h(u_1)=h(u_2)$.
4. **Different windings.** By T6 the depth is at least half a lap. Working through parity, the only possibility is that $u$ is the antipodal previous crossing of $v$'s two strands (T8): $c_1$ lies on one of $v$'s strands and $c_2$ on the other.
5. Strand states pass unchanged through the unique blocks below $u$. So each strand's meeting register arrives at $v$ holding the hash its child-of-$u$ wrote: $h(u_1)$ on one, $h(u_2)$ on the other.
6. $v$'s crossing check forces the two to be equal. Contradiction. ∎

**Elastic defects.** These change only the local faces. Expansion faces are triangles $(E;\,\cdot,\text{source})$, and contraction faces are quads around the sink. By the spacing rule every adjacent pair of parents still shares exactly one parent, so step 3 carries over. Strands still cross in cyclic order, so step 4 carries over.

### T8. Shards, meetings, antipodes
- **Shards.** Over any $P$ consecutive layers, the $P\times P$ blocks correspond one-to-one with the $P\times P$ strand pairs (block in layer $t$ on left strand $\alpha$ ↦ strands $(\alpha,\alpha-t)$). So there are exactly $P^2$ shards, and each pair meets exactly once per $P$ layers, in layer $t\equiv\alpha-\beta$.
  **[Lean: `Weave.Shards.layersEquivShards`, `card_shards`, `meets_once`]**
- **Next meeting.** A pair's next meeting is exactly $P$ layers later, laterally shifted by $P$ units, which is half of $W=2P$: the antipode.
  **[Lean: `Weave.Shards.next_meeting`, `meeting_is_antipode`]**
- **Elastic shard count.** An expansion or contraction adds or removes one strand pair, taking shards from $P^2$ to $(P\pm1)^2$.
  **[Lean: `Weave.Shards.shards_after_expand`, `shards_after_contract`]**

### T9. Elasticity conserves coins
- **Adoption.** It moves a retiring strand's count into the adopting strand's total unchanged. **[Lean: `Weave.Slots.adopt_conserves`]**
- **Sources** open with count 0.
- **Compaction** is relocation (T3).

Hence the full-ring sum of T3 still equals total minted across any sequence of deformations. **[argument]**

### T10. Constant work
Every block runs one step of one circuit. The following are all fixed constants, and the circuit's size depends on nothing else:
- parent slots (3, padded);
- move slots $K$ and compaction slots $K_c$;
- tree depths $D$, $\log_2 A$, $R$.

Chain age, Saros area and $P$ never enter. **[argument]**

### Main theorem (soundness)
**Assumptions.**
- **A1 (PCD knowledge soundness).** HyperNova+CycleFold PCD is knowledge-sound for a fixed compliance predicate at chain depth. This is heuristic per I5; it is formal in the AROM for the CCGOS'23 construction.
- **A2 (hash).** Poseidon2 is collision-resistant, giving Merkle binding and unique strand ids and birth tags.
- **A3 (signatures).** Schnorr on Vesta is EUF-CMA (discrete log in the random-oracle model).
- **A4 (commitment keys).** The hash-to-curve keys have no known relations.

**Statement.** Suppose an adversary outputs an accepting certificate for block $v$. Then, except with probability bounded by the advantages against A1–A4, there is an extractable history of $\mathrm{cone}(v)$ with these properties:
1. it is consistent (T7);
2. every block in it obeys the compliance rules;
3. coins are exclusive (T2);
4. strand counts across any full ring equal the total minted (T3, T9);
5. every spend of an honest key was signed by it;
6. every slot opening against $v$'s roots shows a live coin.

**[argument + cited]**

### Corollaries
- **C1. Finality.** A block's cone covers the whole ring once it is $P$ layers deep. So a payment is certificate-final once a certified block exists $P$ layers below it. (PoW confirmations are separate.)
- **C2. Equivocation is a liveness fault.** Conflicting versions can never meet inside any certified cone (T7). The region stalls until fork choice resolves it.
- **C3. Quads suffice shallowly.** For histories less than $P-1$ layers deep, the adjacency check alone gives consistency (T6). The crossing check exists only for the wrap-around.
- **C4. Throughput.** Throughput is $P\cdot K/\tau$ moves per second: linear in $P$, at constant per-block work (T10). Adoption-driven growth of $P$ is the only scaling knob.

---

## References
- Gentry, Wichs. *Separating SNARGs from all falsifiable assumptions*. STOC'11 (ePrint 2010/610).
- Tamassia, Triandopoulos. *Computational bounds on hierarchical data processing*. ICALP'05.
- Chen, Chiesa, Gur, O'Connor, Spooner. *Proof-carrying data from arithmetized random oracles*. EUROCRYPT'23 (ePrint 2023/587).
- Khovratovich, Rothblum, Soukhanov. *How to prove false statements*. ePrint 2025/118.
- Kothapalli, Setty. *HyperNova*. ePrint 2023/573.
- Kothapalli, Setty. *CycleFold*. ePrint 2023/1192.
- Nguyen, Boneh, Setty. *Revisiting the Nova proof system on a cycle of curves*. ePrint 2023/969.
- Zheng, Gao, Guo, Xiao. *KiloNova*. ePrint 2023/1579.
- Maitin-Shepard, Tibouchi, Aranha. *Elliptic curve multiset hash*. Comput. J. 2017.
- Boneh, Chen. *LatticeFold+*. ePrint 2025/247.
- Nguyen, Setty. *Neo*. ePrint 2025/294.
- Bünz, Chiesa, Fenzi, Wang. *WARP*. ePrint 2025/753.
