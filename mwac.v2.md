# MimbleWimble Atomic Coins
> A MimbleWimble-inspired ledger of non-hiding, unique but fungible coins. Each strand carries a small certificate that is *edited* block by block rather than re-derived. A folding proof (HyperNova + CycleFold) travels with it. Every block runs the exact same circuit, so a prover does the same work per block forever, however old or wide the chain gets. The chain scales by adding strands, not by making blocks heavier.

## A Transaction
Coins live on Vesta, a curve whose arithmetic is native inside the proof (§ Setup). Alice's coin is her public point,
$$
C_A := r_A G
$$
and Bob wants it to be his:
$$
C_B := r_B G
$$
A coin also has a **place**: it sits in one *slot* of one *strand*. A slot stores the owner point and a birth tag, $(C, \text{born})$. The birth tag is the creating block's id plus the output index, so it is unique even when someone reuses the same key.

To pay Bob, Alice **signs** with $r_A$ (Schnorr) a message naming:
- her slot,
- its birth tag,
- Bob's point $C_B$.

The block producer then:
1. empties Alice's slot;
2. writes $(C_B, \text{born}')$ into an empty slot on either of the block's two strands. Picking the strand is the **reroute**.

The v1 excess $X_{A\to B}$ and its PoK are gone. The signature authorises the move, and the slot gives the coin its identity, so equal points no longer cause ambiguity.

## Aggregation
A transaction takes many input slots and produces the same number of outputs:
$$
T := (I := \{\text{slots}\},\ O := \{C'_i\},\ \{\sigma_i\})
$$
The block's proof checks every $\sigma_i$ and that $|I| = |O|$. Each input–output pair is one **move**, and a block carries at most $K$ moves.

Signatures are consumed inside the proof and never stored, so nothing needs to be aggregated. The certificate does not grow with the number of transactions. BLS is dropped because pairings are expensive inside a proof, while Schnorr on Vesta is cheap.

## Cut-through
Say a coin makes its way $A \to B \to C$:
- **Within one block,** the producer writes only $C$'s output. $B$'s coin never touches a slot.
- **Across blocks,** a strand only ever holds live coins. Spent history drops out of the certificate automatically.

## Exclusivity certificate
Each strand carries a certificate:
$$
\text{Cert}_s := (\text{root}_s,\ n_s)
$$
- $\text{root}_s$ commits to the strand's slots:
  - a **main tree**: a Poseidon2 Merkle tree of fixed depth $D$, holding $2^D$ slots;
  - up to $A$ **adopted trees** inherited from retired strands (§ Elasticity).
- $n_s$ counts the occupied slots across all of them.

**Editing, not re-deriving.** Every change to a slot updates one root-to-leaf path:
- **Spend:** show the slot's current contents, check the signature, write "empty", and recompute the root.
- **Create:** show the slot is empty, write the coin, and recompute the root. Creates go only into the main tree.

The equation that must hold is $\text{root}_{\text{after}} = \text{edit}(\text{root}_{\text{before}}, \text{opened slots})$.

**Why this gives exclusivity.** A coin *is* a slot on exactly one strand. Spending means proving what the slot holds and then emptying it. A second spend of the same coin finds the slot empty and fails.

**Why parents' certificates are not summed.** Summing two parents' certificates counts their shared grandparent twice. It also lets a coin spent on both sides of a diamond cancel to "minus one", which hides a double-spend. Instead, each strand's certificate is simply handed on: a block receives one strand from each parent, edits them, and passes each one to the next block along that strand.

## Scarcity certificate
The equation each block must satisfy:
$$
n^{\text{in}}_L + n^{\text{in}}_R + \text{minted} \stackrel{?}{=} n^{\text{out}}_L + n^{\text{out}}_R
$$
- Per transaction, $|I|=|O|$.
- Minting is allowed only in the coinbase, capped by the schedule for that height.

Across the cylinder, summing $n_s$ over every strand along a full ring equals the total ever minted. Anyone holding all the ring's strand certificates can check that.

**The proof is what makes the equations trustworthy.** A root and a count are just numbers, and anyone can write down any numbers. What makes them trustworthy is a proof that every edit, from genesis to this block, followed the rules. Re-checking that history would grow with the chain. So the proof is **folded**: each block absorbs its parents' proofs into one fixed-size accumulator (§ The certificate scheme).

### Strategies considered
- **KZG over hash-to-scalar roots.** Merging multiplies polynomials instead of adding them, and the committed roots don't bind to the coins. Dropped.
- **LWE points, check that errors ≈ 0.** The error grows with every merge until the check means nothing. Dropped.
- **Plain sums of coin points.** All coins share one generator, so different coin sets with equal sums look identical. That hides double-spends and coin splitting. Dropped.
- **KZG slot tables** (constant-cost edits). Rejected: they need a trusted setup and pairings, and wallets must keep their own openings fresh. Merkle trees cost a fixed amount anyway, because the depth is fixed.
- **Plain Nova.** Nova folds two instances at a time. A block with 3 parents would chain 5 folds, and Nova carries an error vector that doubles the hand-off.
- **HyperNova + CycleFold: chosen.** HyperNova folds all parents in **one** step (multi-folding, via sum-check) and has no error vector. Its constraints can be high degree, which makes Poseidon about 3× cheaper. CycleFold handles the curve arithmetic.

---
# The certificate scheme

## Objective
The prover should get the same guarantee from the chain as it evolves, using the same compute: "everything above me is valid". That holds however old the chain is, however large the Saros, and however wide the circumference grows through elasticity. The hand-off between producers and the light-client certificate are also fixed-size.

## Model
Throughout, **$P$ = circumference in blocks** (blocks per ring). It is also the number of left strands, and also the number of right strands.

### The two consistency checks
Exclusivity breaks if two different versions of the same earlier block both feed into one block, because a coin could be spent once in each version. A block rules this out with two comparisons of block hashes:

```
        G              Adjacency check:
       / \             every two side-by-side parents must name the same
     P1   P2           shared parent G. (A parent with a single parent
       \ /             counts that one as both its left and right.)
        B

   ...meet at X ... (P layers: half way round the cylinder) ... meet again at B
                       Crossing check:
                       B's two strands last crossed at the antipode.
                       Each strand remembers whom it last met;
                       both must remember the same block X.
```

- **Adjacency check.** This covers every overlap between the parents' histories except the one that wraps around the cylinder.
- **Crossing check.** This covers the wrap-around; it is the "eclipse at the antipode" in `index.md`.
  - Each strand carries a **meeting register**: an *indexed* Merkle tree of fixed depth $R$, keyed by the other strand's id. Each entry holds the hash of the block where the two strands last crossed.
  - A strand's id is the hash of the block that created it, so ids are never reused and never collide.
  - $B$ reads its two strands' entries for each other, which must be equal, or both absent if they have never met. It then records its parents as the new meetings. A first meeting inserts a new entry; the indexed tree proves the key wasn't there.

If a conflicting version of some block exists, no block can pass both checks with the two versions in its history. That region stalls until fork choice resolves it: a liveness fault, never a broken ledger. Any equivocation is caught within $P$ layers, so **a payment is certificate-final once a certified block exists $P$ layers below it**. At that point the block's history covers the whole ring.

### What a block does
Every block runs **one step of the same circuit**. All of the following are fixed: the parent slots (3, with unused ones padded by a fixed dummy), the move slots ($K$), the compaction slots ($K_c$), and the tree depths.
1. **Take from each parent** its header, the strand certificate coming this way, and its accumulator.
2. **Adjacency check and crossing check** (above).
3. **Apply up to $K$ moves and $K_c$ compaction relocations.**
   - Spend and create are described above.
   - A relocate moves a coin between slots of the block's strands without changing its owner, so it needs no signature.
   - Update counts, then enforce $|I|=|O|$ per transaction and the mint cap.
4. **Fold** every parent's running accumulator and last-step instance, together with this step, into one accumulator. This is a single HyperNova multi-fold; curve operations on commitments go through CycleFold.
5. **Publish** the header, the two outgoing strand certificates, and the accumulator.

### Elasticity
The lattice deforms only at two kinds of defect, matching `elastic.webp`. A defect adds or removes one **strand pair** (one left strand plus one right strand). That changes the circumference by one block per ring and the shard count from $P^2$ to $(P\pm1)^2$.

**Expansion.** A block $E$ declares *expand* and gets a third child directly below it.
- That child is a **source**: its only parent is $E$.
- The source opens a new left strand and a new right strand: empty main trees, $n=0$, empty meeting registers, and ids equal to the source's hash.
- The ring below is one block wider.

**Contraction.** A block $S$ declares itself a **sink**: its two strands end there, and its only child $C$ lies directly below it. $C$ has three parents (left, $S$, right).
- $C$ **adopts** the two retiring certificates. Each one becomes an *adopted tree* inside one of $C$'s outgoing strands.
- This costs a few path updates, whatever the number of coins.
- Adopted coins stay spendable. Their Merkle paths are just $\log_2 A + 1$ levels longer.
- The ring below is one block narrower.

**Compaction.** Every block may relocate up to $K_c$ coins from adopted trees into its main trees, at no signature cost. Adopted trees also empty naturally as their coins are spent. An adopted tree whose count reaches 0 is dropped, freeing the slot.

**Rules** (all enforced by the circuit):
1. **Trigger.**
   - Each strand carries a running average of the time between its blocks.
   - A block may *expand* only if both its strands average faster than the target $\tau$ by a margin $\delta$, i.e. hash power is outpacing the ring.
   - A block may *sink* only if both average slower than $\tau$ by $\delta$.
   - The margin stops oscillation.
2. **Spacing.** No block may expand or sink if any of its parents is a source, a sink, an expansion, or a contraction child. Defects therefore never touch, and every merge still has exactly one shared parent per adjacent pair.
3. **Room.**
   - A sink is allowed only if its strands hold no adopted trees.
   - Its child must have a free adopted-tree slot on each outgoing strand.
   - Otherwise the contraction simply happens somewhere else. This is liveness pressure, never a safety issue.
4. **Shards.**
   - When a strand retires, every shard that included it dissolves and its members join neighbouring shards.
   - When a strand is born, new shards open for any prover to join.

Capacity per strand and work per block never change; elasticity only changes *how many* strands exist. Throughput grows with adoption while each prover's work per block stays flat. Each shard authors one block every $P$ layers, so more strands also means more downtime between turns.

### Interfaces
| Interface | What it does here |
|---|---|
| $\mathsf{Init}$ | Genesis strands get empty trees, counts 0, and empty registers. Their ids are fixed constants. Each starts from the base-case accumulator. |
| $\stackrel{+}{\to}$ | One step: edits to slots, count updates, and one multi-fold. |
| $\stackrel{?}{\to}$ | Check the final accumulator, or a compressed proof of it (§ Cost). Two certificates combine only through a block that passes the adjacency and crossing checks. That condition is what makes "valid + valid = valid" safe. |
| $\stackrel{v?}{\to}$ | A Merkle path from slot $i$ to a certified $\text{root}_s$: $D$ hashes, or $D+\log_2 A+1$ for an adopted coin. |

## Properties
1. **Mergeable:** parents' certificates combine at every block, conditioned on the two checks.
2. **Cancellation by identity:** a spend empties one specific slot. A slot holds 0 or 1 coins, so duplicates and multiplicity can't be ambiguous.
3. **Cardinality survives merge, cut-through and elasticity:** the count equation holds at every block. Adoption carries counts over unchanged. Full-ring sums equal total minted.
4. **Adversarial soundness:** a forged certificate requires breaking the folding proof, Poseidon2, or Schnorr (§ Angles of attack).
5. **Constant work and size:** one fixed circuit, one step per block. Nothing depends on chain length, Saros size, or circumference.

## Parameters
Chosen so a commodity machine proves a block well inside a layer. All constraint and time figures are **estimates** from published component costs, not measurements. Re-derive them once a prototype exists.

| Parameter | Value | Why |
|---|---|---|
| $D$ (main tree depth) | 20 | ~1M coins per strand, about $2\times10^{9}$ total at $P=1024$. Capacity scales with $P$, so a deeper tree isn't needed. |
| $A$ (adopted-tree slots) | 4 | Enough for repeated contractions while compaction catches up. Adds 3 levels to adopted paths. |
| $R$ (register depth) | 32 | Indexed tree with room for $2^{32}$ strand ids ever, so it never needs garbage collection. |
| $K$ (moves per block) | 32 | Keeps the step circuit near $2^{19}$ variables (below). |
| $K_c$ (compaction relocations) | 8 | A full adopted tree drains in about $2^{17}$ layers even if no owner touches it. |
| $\tau$ (target layer time) | 10 s | Covers proving (~1 s) plus receiving up to 3 parent hand-offs (~50 MB, see below) on a 100 Mbit/s link. |
| $\delta$ (elastic margin) | 25% | Hysteresis. |

**Throughput:** $P \cdot K / \tau$ moves per second, i.e. $3.2\,P$/s. That is about 3,300/s at $P=1024$, and it doubles every time adoption doubles the circumference. Work per block does not change.

## Cost
Assumptions: Pallas/Vesta, Poseidon2 as degree-5 CCS gates (about 100 variables per 2-to-1 hash, versus about 250 in R1CS), $D=20$, $K=32$.

| Part (per block) | Witness variables (approx.) |
|---|---|
| One move: spend path + create path (~46 hashes) + Schnorr check | ~9k |
| 32 moves + 8 compaction relocations | ~360k |
| Meeting registers: two reads + two indexed updates (depth 32) | ~30k |
| Multi-fold of 3 parents (running + last-step instances, padded), sum-check verifier, CycleFold bookkeeping | ~60–80k |
| Header, adjacency checks, counts, timestamps, triggers | ~10k |
| **Total** | **~470k ≈ $2^{19}$** |

- **Prover per block:** one multi-scalar multiplication of ~$2^{19}$ points on Pallas, plus a degree-5 sum-check and a small CycleFold step. Roughly **1 s** on a current laptop CPU. It is identical for every block forever.
- **Hand-off to child producers (raw, decided):** the accumulator's instance plus its witness vector, about $2^{19}\times 32$ B ≈ **16 MB** per parent.
  - HyperNova has no error vector, which is half of what Nova would send.
  - Raw hand-off is required: only the holder of the witness can fold it further.
  - The *last-step* witness never needs sending. It is rebuilt from public data (block body, parent headers, strand data).
- **Light clients:** anyone holding an accumulator can produce a compressed proof on demand, about 10–50 KB (Spartan over Pasta). Wallets and explorers check only that. Producers never need to compress, so compression costs nothing on the critical path.
- **Partial node storage:** two strands' trees, $2\times2^{20}$ slots ≈ 150 MB with Merkle nodes. Following a strand means applying at most $K+K_c$ edits per layer.

## Setup & trust
- **Curves:** Pallas/Vesta, roughly 126-bit classical security.
  - These need no pairings and no trusted setup.
  - Proofs run over Pallas's scalar field, so Vesta arithmetic (coins, signatures) is native.
  - CycleFold proves the Pallas commitment arithmetic on Vesta.
- **Commitment keys:** generated by hash-to-curve from a public seed. Nobody knows relations between them.
- **Poseidon2:** standard published parameters for the Pallas scalar field.
- **Light-client compression:** Spartan, which is transparent.
- **No ceremony anywhere.**

## Angles of attack
Each item: what an attacker would try → what stops it, or what to audit.

**Certificate & edits**
- **Write into an occupied slot** (destroying a coin, or duplicating one together with a relocate) → every write must prove the slot's *old* contents first.
- **Ambiguous empty leaf** → a coin leaf must never hash to the empty marker. Constrain it.
- **Non-boolean path bits** (the classic under-constrained Merkle bug: the prover picks arbitrary siblings) → constrain every direction bit to 0/1 and every index to its exact width.
- **Leaf and internal node with the same hash** → domain-separate leaf, node, adopted-tree, register, and Fiat–Shamir hashing.
- **Signature replay onto a refilled slot owned by the same key** → the signed message includes the birth tag.
- **Invalid points** → check that points are on the curve and not the identity. Vesta has prime order, so no cofactor issues.
- **Signature nonce reuse** → a wallet-side key leak, outside the proof's control. Use deterministic nonces.
- **Supplied rather than derived values** → counts, heights, strand ids, positions, mint cap, timestamps averages: all *computed* in the circuit from the parents, never taken from the prover.
- **Creating into an adopted tree** (bypassing capacity, or re-filling retired space) → creates are constrained to the main tree.

**Consistency checks**
- **Edge cases that skip a check** (genesis, sources, sinks, contraction children, padded parents) are where equivocation would slip in. Each skip must be forced by topology, not by a prover-set flag.
- **Fake first meeting** (claiming two strands never met, to dodge the crossing check) → the indexed tree must prove the key is absent: the neighbouring "low" entry's key must be strictly below the new key, and its "next" pointer strictly above.
- **Strand id collisions** → ids are full-width hashes of the birth block, never truncated.
- **Spending before finality** → equivocation is caught within $P$ layers. Before that, coins received should be treated as unconfirmed.

**Elasticity**
- **Faked timestamps to force expansions or sinks** → triggers use per-strand averages with a margin, and consensus bounds timestamps (median-past, max-future). The worst an attacker can do is churn or draining pressure, which is a liveness issue. The spacing rule stops expand–contract oscillation.
- **Retiring a strand without handing over its coins** → the sink's strands must arrive at the child as adopted trees with their counts. The count equation includes adopted counts.
- **Dropping a non-empty adopted tree** → only allowed when its count is 0.
- **Filling a strand's $2^D$ slots with dust** → dust rules or fees, plus expansion.

**HyperNova folding**
- **Incomplete Fiat–Shamir transcript** (a "Frozen Heart"-style bug: the prover picks values after seeing the challenge) → every sum-check round message, all folded instances, the folding challenge, the public IO, and the circuit digest must be absorbed before each challenge.
- **Sum-check degree** → every round polynomial must be checked to have the stated degree. If a round's degree isn't checked, a cheating prover gets the extra freedom it needs.
- **Evaluation point not bound to the transcript** → each folded instance's evaluation point and claimed values must come from the transcript, not from the prover.
- **Running instance not bound to public IO** → each step's public input includes a hash of (circuit digest, block id, state, running accumulator, CycleFold accumulator). The original Nova-on-a-cycle implementation had a soundness bug exactly here (Nguyen–Boneh–Setty, 2023). Build on fixed code.
- **Base-case and dummy parents** → "this is genesis" and "this parent slot is empty" must follow from topology. The dummy must be one fixed public instance. A prover-chosen flag or dummy would let them skip verification.
- **Incomplete final check** → the decider must fully check *both* accumulators: the primary (witness against its commitment, evaluation claims) and the CycleFold one. Skipping CycleFold lets curve arithmetic be faked.
- **Commitment keys with known relations** → a commitment could then open to anything. That is why keys come from hash-to-curve. The key must also be long enough for the whole witness.
- **Witness withholding** → a producer that keeps its 16 MB accumulator witness to itself stalls its children (liveness, not safety). The hand-off size is also a bandwidth/DoS surface; rate-limit by stake or PoW.
- **Two children folding the same parent** is safe. Each child's challenge already includes its own data.

**CycleFold**
- **Mismatch between the primary circuit and the CycleFold instances** → the points and scalars the primary uses must equal the CycleFold instances' public inputs, bit for bit.
- **Non-canonical encodings** → non-native values are split into limbs. Range-check every limb so one value has one encoding, and range-check every scalar's bit decomposition.
- **Exceptional cases in curve addition** (identity, doubling) → use complete addition formulas.
- **Folding several CycleFold instances per block** (one per combined commitment) → every one must be folded and none skipped.

**Hash / Fiat–Shamir inside the circuit**
- **Fiat–Shamir with the hash computed in-circuit** → recursion requires the Fiat–Shamir hash (Poseidon2) to run inside the circuit, which is outside what random-oracle proofs cover. The 2025 Khovratovich–Rothblum–Soukhanov attack exploits exactly this, though only when the attacker chooses the circuit. Here the circuit is fixed and its digest is hashed into every transcript, which is the known mitigation. Treat it as an assumption, not a theorem.
- **Poseidon cryptanalysis** → reduced-round attacks are active research. Use full recommended rounds and keep the hash swappable.

**Curves & long term**
- **Pasta security margin** → roughly 126-bit classically.
- **Quantum attacks** → discrete-log folding and Schnorr both break. Migration path: keep the Merkle certificates as they are and swap the folding layer for a hash- or lattice-based one (WARP, LatticeFold+, Neo), plus a post-quantum signature.

**General**
- **Under-constrained circuits** → most real-world ZK failures are missing constraints, not broken math. Audit with constraint-analysis tools and differential tests against a plain reference implementation.

## Status
Every v2 open item is now settled:
- **Parameters** are in § Parameters.
- **Hand-off** is raw; compression is on demand for light clients.
- **Contraction** works by adoption plus compaction. No drain window is needed.
- **Percolation** in `index.md` matches this scheme.

What remains is validating the cost estimates with a prototype, and compiling the Lean files once a toolchain is available.

**Where the math lives:**
- [proofs.md](./proofs.md) has the impossibility results, theorems and corollaries behind every choice above, plus the pitfalls this repo hit on the way.
- [lean/](./lean/README.md) has their formal statements.
