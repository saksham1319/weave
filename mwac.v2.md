# MimbleWimble Atomic Coins
> A MimbleWimble-inspired ledger of non-hiding, unique but fungible coins. Each strand carries a small certificate that is *edited* block by block rather than re-derived. A folding proof (Nova + CycleFold) travels with it, so every prover does the same fixed amount of work per block no matter how old or wide the chain gets.

## A Transaction
Coins live on Vesta, a curve chosen because its arithmetic is native inside the proof (§ Setup). Alice's coin is her public point,
$$
C_A := r_A G
$$
and Bob wants it to be his:
$$
C_B := r_B G
$$
A coin also has a **place**: it sits in one *slot* of one *strand*. A slot stores the owner point and a birth tag, $(C, \text{born})$. The birth tag is the position of the block that created the coin plus its output index, so it is unique even when someone reuses the same key.

To pay Bob, Alice **signs** a message with $r_A$ (Schnorr). The message names:
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
The block's proof checks, inside the circuit, that every $\sigma_i$ is valid and that $|I| = |O|$.

Signatures are consumed inside the proof and never stored, so nothing needs to be aggregated. The certificate does not grow with the number of transactions. BLS is dropped because pairings are expensive inside a proof, while Schnorr on Vesta is cheap.

## Cut-through
Say a coin makes its way $A \to B \to C$:
- **Within one block,** the producer writes only $C$'s output. $B$'s coin never touches a slot.
- **Across blocks,** a strand only ever holds live coins. Spent history drops out of the certificate automatically, so cut-through is permanent and free.

## Exclusivity certificate
Each strand carries a certificate:
$$
\text{Cert}_s := (\text{root}_s,\ n_s)
$$
- $\text{root}_s$ is the root of a fixed-depth Merkle tree (Poseidon2) over the strand's $2^D$ slots. An empty slot is a fixed "empty" leaf.
- $n_s$ is the number of occupied slots.

**Editing, not re-deriving.** Every change to a slot updates one root-to-leaf path:
- **Spend:** show the slot's current contents (path to the old root), check the signature, replace it with "empty", and recompute the root.
- **Create:** show the slot is empty, write the new coin, and recompute the root.

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

**The proof is what makes the equations trustworthy.** A root and a count are just numbers, and anyone can write down any numbers. What makes them trustworthy is a proof that every edit, from genesis to this block, followed the rules. Re-checking that history would grow with the chain. So the proof is **folded**: each block absorbs its parents' proofs into one constant-size accumulator (§ The certificate scheme).

### Strategies considered
- **KZG over hash-to-scalar roots.** Merging multiplies polynomials instead of adding them, and the committed roots don't bind to the coins. Dropped.
- **LWE points, check that errors ≈ 0.** The error grows with every merge until the check means nothing. Dropped.
- **Plain sums of coin points.** All coins share one generator, so different coin sets with equal sums look identical. That hides double-spends and coin splitting. Dropped.
- **Proof carried along with the certificate (folding): chosen.** Nova folding, with CycleFold for the curve arithmetic, over a single fixed step circuit. Every block runs the same circuit, so every block costs the same.

---
# The certificate scheme

## Objective
The prover should get the same guarantee from the chain as it evolves, using the same compute: "everything above me is valid". That holds however old the chain is, however large the Saros, and however wide the circumference grows through elasticity. The certificate a block passes on is also fixed-size.

## Model
### The two consistency checks
Exclusivity breaks if two different versions of the same earlier block both feed into one block, because a coin could be spent once in each version. A block rules this out with two comparisons of block hashes:

```
        G              Quad check:
       / \             both parents must name the same grandparent G.
     P1   P2
       \ /
        B

   ...meet at X ... (half a lap of the cylinder) ... meet again at B
                       Crossing check:
                       B's two strands last crossed at the antipode, W/2 layers up.
                       Each strand remembers whom it last met;
                       both must remember the same block X.
```

- **Quad check.** This covers every overlap between the parents' histories except the one that wraps around the cylinder.
- **Crossing check.** This covers the wrap-around; it is the "eclipse at the antipode" in `index.md`.
  - Each strand carries a small **meeting register**: a Merkle tree of fixed depth $R$, recording, for each other strand, the hash of the block where they last crossed.
  - $B$ reads its two strands' entries for each other, compares them, and records its parents as the new meetings.

If a conflicting version of some block exists, no block can pass both checks with the two versions in its history. That region stalls until fork choice resolves it: a liveness fault, never a broken ledger. Equivocation is caught within half a lap at most, so **a payment is final once a certified block exists $W/2$ layers below it.**

### What a block does
Every block runs the **same step circuit**:
1. **Take from each parent** its header hash, the strand certificate coming this way, and its folded proof (accumulator).
2. **Quad check and crossing check** (above).
3. **Apply up to $k$ ops per step.** Each op is a spend, a create, or a relocate.
   - Spend and create are described above.
   - A relocate moves a coin between the block's two strands without changing its owner, so it needs no signature.
   - Update counts, then enforce $|I|=|O|$ per transaction and the mint cap.
4. **Fold** the parents' accumulators and this step into one accumulator (Nova). Curve operations on commitments go through CycleFold.
5. **Publish** the header, the two outgoing strand certificates, and the accumulator.

A block with more than $k$ ops runs a few more identical steps, chained inside the block. Block size is capped, so the number of steps per block is capped too.

### Elasticity
The step circuit always accepts up to **3 parents**; unused inputs are padded.
- **Expansion** (a block with 3 children) creates a strand with an empty tree, $n=0$, and empty meeting registers.
- **Contraction** (a block with 3 parents) retires a strand. This is only allowed when it is empty. Producers drain it ahead of time with relocates.

Capacity per strand ($2^D$ slots) and work per block never change; elasticity changes only the *number* of strands. Throughput grows with adoption while each prover's work stays flat. More strands means each prover waits longer between turns: the downtime noted in `index.md`.

### Interfaces
| Interface | What it does here |
|---|---|
| $\mathsf{Init}$ | Empty trees on every genesis strand, counts 0, empty registers, and the base-case accumulator. |
| $\stackrel{+}{\to}$ | One step: edits to slots, a count update, and one fold. |
| $\stackrel{?}{\to}$ | Check the final folded accumulator, or a compressed proof of it (§ Cost). Two certificates combine only through a block that passes the quad and crossing checks. That condition is what makes "valid + valid = valid" safe. |
| $\stackrel{v?}{\to}$ | A Merkle path from slot $i$ to a certified $\text{root}_s$: $D$ hashes. |

## Properties
1. **Mergeable:** parents' certificates combine at every block, conditioned on the two checks.
2. **Cancellation by identity:** a spend empties one specific slot. A slot holds 0 or 1 coins, so duplicates and multiplicity can't be ambiguous.
3. **Cardinality survives merge and cut-through:** the count equation holds at every block, and full-ring sums equal total minted.
4. **Adversarial soundness:** a forged certificate requires breaking the folding proof, Poseidon2, or Schnorr (§ Angles of attack).
5. **Constant work and size:** the circuit, the tree depths, and the fold count are all fixed. Nothing depends on chain length, Saros size, or circumference.

## Cost
These are estimates to size the system, not measurements. Assumptions: Pallas/Vesta, Poseidon2, $D = 24$ (16.7M coins per strand), $R = 16$, $k = 8$.

| Part | Constraints (approx.) |
|---|---|
| One slot edit (old path + new root, $2D$ hashes) | ~12k |
| One Schnorr check on Vesta (native) | ~5k |
| Folding verifier per accumulator (with CycleFold) | ~10–20k |
| Two meeting-register edits ($2R$ hashes each) | ~16k |
| **One step** (8 ops, up to 3 parents) | **~200–250k** |

- **Prover per step:** one multi-scalar multiplication over about the step size, plus linear field work. This is identical for every step forever.
- **Hand-off to child producers:** the accumulator plus its witness, a few MB. A producer can instead compress to about 10–50 KB with Nova's compressed SNARK (Spartan), at extra prover cost.
- **Light clients:** they check the compressed proof only.

## Setup & trust
- **Curves:** Pallas/Vesta, roughly 126-bit classical security.
  - These need no pairings and no trusted setup.
  - Proofs run over Pallas's scalar field, so Vesta arithmetic (signatures, coins) is native.
  - CycleFold handles Pallas arithmetic on the other curve.
- **Commitment keys:** generated by hash-to-curve from a public seed. Nobody knows relations between them.
- **Poseidon2:** standard published parameters.
- **Optional compression:** Spartan, which is transparent.
- **No ceremony anywhere.**

## Angles of attack
Each item: what an attacker would try → what stops it, or what to audit.

**Certificate & edits**
- **Write into an occupied slot** (destroying a coin, or duplicating one together with a relocate) → every write must prove the slot's *old* contents first.
- **Ambiguous empty leaf** → a coin leaf must never hash to the empty marker. Constrain it.
- **Non-boolean path bits in a Merkle proof** (the classic under-constrained bug: the prover picks arbitrary siblings) → constrain every direction bit to 0/1 and the index to exactly $D$ bits.
- **Leaf and internal node with the same hash** → domain-separate leaf, node, register, and Fiat–Shamir hashing.
- **Signature replay onto a refilled slot owned by the same key** → the signed message includes the birth tag.
- **Invalid points** → check that points are on the curve and not the identity. Vesta has prime order, so no cofactor issues.
- **Signature nonce reuse** → a wallet-side key leak, outside the proof's control. Use deterministic nonces.
- **Supplied rather than derived values** → counts, height, position, and mint cap must all be *computed* in the circuit from the parents, never taken from the prover.

**Consistency checks**
- **Edge cases that skip a check** (genesis, the first step of a block, elastic nodes, padded parents) are where equivocation would slip in. Each skip must be forced by position, not by a prover-set flag.
- **Stale meeting registers after a strand retires and its index is reused** → tag register keys with a strand generation number.
- **Position spoofing** → a position is derived from the parents' positions. Circumference changes from elasticity must re-derive positions the same way at every node.
- **Spending before finality** → equivocation is caught within $W/2$ layers. Before that, coins received should be treated as unconfirmed.

**Nova folding**
- **Incomplete Fiat–Shamir transcript** (a "Frozen Heart"-style bug: the prover picks values after seeing the challenge) → the challenge must hash every instance being folded, the cross-term commitment, the public IO, and the circuit digest.
- **Running instance not bound to public IO** → each step's public input includes a hash of (circuit digest, position, state, primary accumulator, CycleFold accumulator). The original Nova-on-a-cycle implementation had a soundness bug here (Nguyen–Boneh–Setty, 2023). Build on the fixed version.
- **Base-case flag** → "this is genesis" must follow from the position. If a prover can set it freely, they can skip verification anywhere.
- **Incomplete final check** → the decider must fully check *both* accumulators: the primary one (witness, error term, scalar) and the CycleFold one. Skipping CycleFold lets curve arithmetic be faked.
- **Commitment keys with known relations** → a commitment could then open to anything. That is why keys come from hash-to-curve. The key must also be long enough for the whole witness.
- **Witness withholding** → a producer that keeps its accumulator witness to itself stalls its children (liveness, not safety). The witness size is also a bandwidth/DoS surface.
- **Two children folding the same parent** is safe. Each child's challenge already includes its own data.

**CycleFold**
- **Mismatch between the primary circuit and the CycleFold instance** → the points and scalars the primary uses must equal the CycleFold instance's public inputs, bit for bit.
- **Non-canonical encodings** → non-native values are split into limbs. Range-check every limb so one value has one encoding. Range-check the challenge scalar's bit decomposition.
- **Exceptional cases in curve addition** (identity, doubling) → use complete addition formulas in the secondary circuit.
- **Limb arithmetic** where the CycleFold accumulator is folded inside the primary circuit → this is non-native arithmetic, so audit it.

**Hash / Fiat–Shamir inside the circuit**
- **Fiat–Shamir with the hash computed in-circuit** → recursion requires the Fiat–Shamir hash (Poseidon2) to run inside the circuit, which is outside what random-oracle proofs cover. The 2025 Khovratovich–Rothblum–Soukhanov attack exploits exactly this, though only when the attacker chooses the circuit. Here the circuit is fixed and its digest is hashed into every transcript, which is the known mitigation. Treat it as an assumption, not a theorem.
- **Poseidon cryptanalysis** → reduced-round attacks are active research. Use full recommended rounds and keep the hash swappable.

**Curves & long term**
- **Pasta security margin** → roughly 126-bit classically.
- **Quantum attacks** → discrete-log folding and Schnorr both break. Migration path: keep the Merkle certificates as they are and swap the folding layer for a hash- or lattice-based one (WARP, LatticeFold+, Neo), plus a post-quantum signature.

**Elasticity & capacity**
- **Faked timestamp drift** to force expansions or contractions → retiring requires an empty strand, so the worst an attacker can do is create draining pressure, which is a liveness issue.
- **Filling a strand's $2^D$ slots with dust** → dust rules or fees, plus expansion.

**General**
- **Under-constrained circuits** → most real-world ZK failures are missing constraints, not broken math. Audit with constraint-analysis tools and differential tests against a plain reference implementation.

## Open items
- Fix $D$, $R$, $k$, and the block-size cap from target throughput.
- Choose per-block compression versus raw accumulator hand-off.
- Write the drain-window rule for contractions.
- Decide whether `index.md`'s $n^{-1}$ percolation rule is replaced outright. It conflicts with this scheme: certificates are handed on, not summed.
