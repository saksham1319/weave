# Weave Certificates v3: Strand-Linear PCD
> Answer to *"The certificate scheme I need"* (mwac.v2.md). Summary: the object asked for (a mergeable multiset-cardinality accumulator where any two valid certificates merge into a valid one) **cannot exist** for a ledger. The changes it needs are *forced*, not optional. Once they are made, a construction with $O(1)$ certificates and $O(1)$-in-$|M|$ prover work does exist. It is below, with its security statement, cost bounds, and the impossibility results that force its shape.

---

## 0. Verdict

| Requirement (v2) | Status |
|---|---|
| 1. Mergeable certificates | ✅ only **conditionally** (merge must check agreement on the shared past). Unconditional merge-closure is impossible (§2, **I1**). |
| 2. Cancellation by identity & multiplicity | ✅ but not with a multiset sum. Coins become **cells** in per-strand tables, and multiplicity is $\{0,1\}$ by construction. |
| 3. Cardinality survives merge & cut-through | ✅ *implied* by exclusivity + per-tx $\lvert I\rvert=\lvert O\rvert$. A signed cardinality invariant **on its own is worthless** (§2, **I2**). |
| 4. Computational soundness vs. adversarial input | ✅ via knowledge soundness of PCD. Requires ROM/AROM or knowledge-type assumptions; this is **unavoidable** (§2, **I3**). |
| 5. $O(1)$ proving & certificate size, independent of Saros | ✅ Variant **K**: $O(1)$ per op in $\lvert M\rvert$ and $N$. Variant **M** (transparent, plausibly PQ): $O(\log N)$ per op, which is **optimal** for hash-only schemes (§2, **I4**). |

**The core idea.** Stop treating the UTxO set as one multiset that gets *summed* across the DAG. The strands in `index.md` already partition it. Make that partition a **linear (single-owner) resource**: every live coin occupies exactly one cell of exactly one strand table. Strand tables are never added together; they only flow along strands and swap coins where strands cross. Merging then reduces to two $O(1)$ **consistency checks**:

- a *quad* check: the two parents agree on their shared parent;
- a *crossing* check: the two incoming strands agree on where they last crossed, at the antipode.

Proof-carrying data (PCD) carries "every block in my past cone was compliant" forward at constant cost per block. The antipodal crossing check is exactly the *meridian/antipode eclipse* from `index.md`, now with a precise job: it removes the cylinder's one non-contractible cycle.

---

## 1. Setting and notation

**Lattice.** Positions $v=(x,t)$ with $x\in\mathbb Z_W$, $W$ even, $x+t$ even. $W$ is the circumference.
- Parents: $p_L(v)=(x-1,t-1)$, $p_R(v)=(x+1,t-1)$.
- Meet (apex of $v$'s quad face): $q(v)=(x,t-2)$.

**Strands.** Each position lies on two strands:
- $\rho(v)=x-t \bmod W$ (moves down-right);
- $\lambda(v)=x+t \bmod W$ (moves down-left).

$v$ receives strand $\rho(v)$ from $p_L$ and strand $\lambda(v)$ from $p_R$. It emits $\rho(v)$ to $(x+1,t+1)$ and $\lambda(v)$ to $(x-1,t+1)$.

**Strand crossings.** $\rho(v)$ and $\lambda(v)$ meet again exactly when $2(t'-t)\equiv 0 \pmod W$. So their previous crossing is
$$q'(v)=\left(x+\tfrac W2,\; t-\tfrac W2\right),$$
which is the antipode of $v$, $W/2$ layers up. Strands cross every $W/2$ layers, alternating between two antipodal meridians.

**Shard count (closes the `TODO proof` in index.md).** Since $x+t$ is even, $x-t$ is even too, so each family has $W/2$ strands. A strand pair $(\rho,\lambda)$ fixes $2x\equiv\rho+\lambda \pmod W$. That gives two antipodal solutions for $x$, so every pair does cross. There are therefore exactly
$$(W/2)^2 = W^2/4 = \Theta(W^2)$$
committees (Saros-sharing node sets). Each committee can author blocks only once every $W/2$ layers. This is the "prover downtime" mentioned in the Elasticity section.

**Cones.** $\mathcal C(v)$ is the past cone of $v$ (all its ancestors). Within depth $<W/2$ it is a planar diamond. At depth $\ge W/2$ it covers whole rings. Read the Saros as $\mathcal C(v)$ cut at the epoch base.

**Cost symbols.**

| Symbol | Meaning |
|---|---|
| $\lambda_{\sec}$ | security parameter |
| $\lvert M\rvert$ | live coins in the Saros |
| $\lvert X\rvert$ | ops (inputs + outputs) in the block |
| $d$ | in-arity: 2 normally, 3 on contraction |
| $N$ | per-strand table capacity |
| $\lvert F\rvert$ | step-circuit size |

---

## 2. Counterexamples and impossibility results

### Counterexamples to the existing candidates

**C1. Sums of $rG$ over one generator.**
All coins are multiples of one public generator, so $\sum C_i=(\sum r_i)G$, and the certificate only constrains a single scalar.
- *Inflation.* The owner of $r_A$ outputs $k$ coins $r_iG$ with $\sum r_i=r_A$.
- *Invisible double-spend.* Shard 1 runs $C_A\to C_B$ and shard 2 runs $C_A\to C_C$. The merged certificate $(2C_A,\,C_B+C_C)$ looks exactly like an honest spend of two coins $C_X,C_Y$ with $C_X+C_Y=2C_A$.

So the exclusivity certificate does not even certify exclusivity.

**C2. The $n^{-1}$ percolation rule is wrong.**
Unroll $D(v)=\tfrac12D(p_L)+\tfrac12D(p_R)+\Delta(v)$. An ancestor at depth $k$, reached by $\binom kj$ paths, gets weight $\binom kj/2^k$ instead of 1.

Concrete failure: a coin created at $a=(x-1,t-3)$ and spent at $q=(x,t-2)$ leaves residue $\tfrac38-\tfrac12=-\tfrac18$ in $D(v)$. Cut-through fails, and no single node's certificate is the digest of an integer multiset. The scheme only conserves mass summed over a *full ring*, and a partial node cannot see a full ring.

The exact recurrence is inclusion–exclusion over the quad face. It holds for depth $<W/2$, because only there is $\mathcal C(p_L)\cap\mathcal C(p_R)=\mathcal C(q)$:
$$D(v)=D(p_L)+D(p_R)-D(q(v))+\Delta(v)$$
See Appendix A. This still does not give exclusivity (I1).

**C3. KZG over characteristic polynomials.**
$\prod(X-x_i)$ merges by *multiplication*. Multiplying committed polynomials needs a pairing, and you only get one level of that, so merge depth is bounded. The v2 doc's own objections (hash-to-scalar, ECDLP, convolution cost) also stand.

**C4. LWE "error ≈ 0".**
Noise grows linearly with the number of merges, so after about $q/(4B)$ merges the check is meaningless. That bounds the depth. Worse, the adversary chooses its own errors, so this is not a knowledge argument and gives no soundness.

### Impossibility results that force the construction

**I1. Exclusivity is not merge-closed.**
Let $\mathsf{Valid}$ mean "exclusive (multiplicities in $\{0,1\}$) and reachable by valid transactions". Take three individually valid states:
- $q$ holds coin $x$;
- $A = q$, then spend $x\to y$;
- $B = q$, then spend $x\to z$.

Any merge that is a function of the certificates alone must either accept $A\oplus B$ (then $y$ and $z$ are both live: unsound) or reject it (contradicting merge-closure). ∎

So **v2's interface requirement "two valid commitments merge to a valid one" must be weakened** to: merge is valid *if the two histories agree on their common past*. §3 achieves this with the Φ2/Φ3 checks.

**I2. Signed cardinality is not supply.**
In I1, every transaction conserves count, so the signed count $n(A)+n(B)-n(q)=n(q)$ is unchanged. Yet the number of spendable coins, $\sum_x \max(m_x,0)$, has grown by 1, and $x$ sits at multiplicity $-1$.

$\max(\cdot,0)$ is not a group homomorphism, so **no homomorphic digest can track spendable supply**. What must be certified is exclusivity. Cardinality then follows (Lemma 2). The separate scarcity certificate in v2 is redundant once exclusivity is certified.

**I3. Binding is not well-formedness, so knowledge arguments are necessary.**
Take any compressing digest $D:\mathbb Z^U\to\mathbb G$, e.g. ECMH with $|U|^n\gg|\mathbb G|$. Almost every $d\in\mathbb G$ has preimages of every cardinality $n\ge2$. So the statement "$\exists M:\ D(M)=d\wedge |M|=n$" is trivially true and says nothing.

The only meaningful notion of well-formedness is that **a valid history producing $(d,n)$ is known**. An $O(1)$-size, $O(1)$-time certificate for that is a SNARK for NP with unbounded witness. By Gentry–Wichs (STOC'11), adaptive soundness of such an object cannot be proved from falsifiable assumptions via black-box reductions.

**Necessary relaxation:** soundness in the ROM/AROM, or under knowledge-type assumptions (AGM, KEA). Incremental $O(1)$ work per node additionally forces the certificate to be **PCD**.

The only alternative is honest-majority committee signatures (a BLS threshold signature per Saros council). Those are $O(1)$, but their security is shard-takeover-bounded, which is strictly weaker.

**I4. The membership/update floor.**
Spends delete from a dynamic set. Any *hash-based* authenticated dictionary of size $n$ has $\Omega(\log n)$ worst-case update and proof cost (Tamassia–Triandopoulos, ICALP'05). Strict $O(1)$ therefore requires an algebraic vector commitment, which brings a trusted setup (KZG) and loses post-quantum security.

**I5. Recursion puts the Fiat–Shamir hash inside the circuit.**
ROM proofs do not cover that. Khovratovich–Rothblum–Soukhanov (ePrint 2025/118) break a real GKR-based argument when its FS hash is circuit-evaluable.

Formal PCD security for arbitrary depth exists in the **AROM** (Chen–Chiesa–Gur–O'Connor–Spooner, EC'23). Folding-based PCD at polynomial depth is **heuristic**. This is stated as an explicit assumption in §4.

---

## 3. Construction: Strand-Linear PCD (SL-PCD)

### 3.1 State

Each strand $s$ carries a **strand state**
$$S_s=(\mathsf{Com}_s,\; n_s,\; \mathsf{Reg}_s)$$
- $\mathsf{Com}_s$ is a commitment to a table $T_s\in\mathbb F^N$.
  - Cell $T_s[i]=0$ means empty.
  - Otherwise $T_s[i]=\mathsf{enc}(pk,\mathit{id})$, where $\mathsf{enc}$ is a collision-resistant hash constrained to be $\neq0$.
  - $\mathit{id}=(\text{pos}_{\text{creator}},\text{tx},\text{out})$ is unique within any consistent history.
- $n_s$ is the number of non-empty cells.
- $\mathsf{Reg}_s$ is a commitment to $W/2$ **crossing registers**, keyed by the opposite-family strand index. Each holds the hash of the block where $s$ last crossed that strand.

Block $v$'s public state:
$$z_v=(\text{pos}_v,\ h_{p_L},\ h_{p_R},\ S'_{\rho(v)},\ S'_{\lambda(v)},\ \mathsf{acc}_v), \qquad h_v=H(z_v\setminus\mathsf{acc}_v,\ \text{txroot})$$
$\mathsf{acc}_v$ is the folding running instance. In Variant K it also holds a KZG pairing accumulator $(P,\Pi)\in\mathbb G_1^2$.

### 3.2 Compliance predicate $\Phi(z_v;\,z_{p_L},z_{p_R};\,w_v)$

**Φ1 – Lineage.**
- $z_v$ names $H(z_{p_L})$ and $H(z_{p_R})$.
- The parents' positions are $\text{pos}_v+(\mp1,-1)$.
- Inputs come from the parents: $S^{\text{in}}_\rho := z_{p_L}.S'_{\rho}$ and $S^{\text{in}}_\lambda := z_{p_R}.S'_{\lambda}$.

**Φ2 – Quad agreement.**
$z_{p_L}.h_{p_R} = z_{p_R}.h_{p_L}$. Both parents name the same block at $q(v)$.

**Φ3 – Crossing agreement.**
- Open $\mathsf{Reg}_\rho[\lambda(v)]$ and $\mathsf{Reg}_\lambda[\rho(v)]$, and require them to be equal (both are the hash of $q'(v)$, or both $\bot$ from genesis).
- Then write $\mathsf{Reg}_\rho[\lambda(p_L)] := h_{p_L}$ and $\mathsf{Reg}_\lambda[\rho(p_R)] := h_{p_R}$.

Children write their parent's hash, which avoids self-reference. Along a strand the key advances by 2 per step, so the key being read is never the key being written.

**Φ4 – Ops**, applied in sequence to $T_\rho,T_\lambda$:
- **spend**$(s,i,pk,\mathit{id},\sigma)$: open $T_s[i]=\mathsf{enc}(pk,\mathit{id})$; verify Schnorr $\sigma$ under $pk$ on the tx body; set $T_s[i]\gets0$; $n_s\mathrel{-}=1$.
- **create**$(s,i,pk')$: open $T_s[i]=0$; set $T_s[i]\gets\mathsf{enc}(pk',(\text{pos}_v,\text{tx},\text{out}))$; $n_s\mathrel{+}=1$. Choosing $s$ is the **reroute**: the output goes onto either of the two strands.
- **relocate**$(s,i\to s',j)$: no signature, because the owner does not change. Used for draining strands and rebalancing.
- **Per-tx rule:** #spends = #creates. Coinbase creates at most $\mu(t)$ cells (the supply schedule).

**Φ5 – Recursion.**
- Fold the $d$ incoming running instances together with this step (HyperNova multi-folding / ProtoGalaxy $k$-folding; CycleFold for the non-native group operations).
- Variant K: fold each new KZG claim into $(P,\Pi)$ with an FS challenge $r$: $(P,\Pi)\mathrel{+}=r\cdot(A_i+\omega^i\pi_i,\ \pi_i)$, where $A_i=\mathsf{Com}-a_i[1]_1$. Merge parents as $(P_L+r'P_R,\ \Pi_L+r'\Pi_R)$.

**Elastic nodes** ($d=3$ in or $3$ out):
- Φ2 is checked for every pair of adjacent parents.
- Φ3 is checked for every pair of strands crossing at $v$.
- A strand is born with $S=(\mathsf{Com}(\mathbf 0),0,\bot)$.
- A strand may be retired only when $n_s=0$. It is drained beforehand by `relocate` over a window of at least $N/|X|_{\max}$ blocks.
- **Required deformation semantics** (this is the "Saros boundary semantics" left open in index.md): the face complex must stay a cellulation of the cylinder in which every bounded face has a unique bottom vertex, and that vertex's adjacent parents bound the face. Lemma 1 then carries over unchanged.

### 3.3 Two table-commitment variants

| | **Variant K** (algebraic, $O(1)$) | **Variant M** (transparent, plausibly PQ) |
|---|---|---|
| $\mathsf{Com}_s$, $\mathsf{Reg}_s$ | KZG over a Lagrange basis on $\langle\omega\rangle$, $\lvert\cdot\rvert=N$ | Poseidon2 Merkle tree, depth $\log N$ |
| Update cell $i$: $a\to b$ | $\mathsf{Com}\mathrel{+}=(b-a)\,L_i$, with $L_i=[\ell_i(\tau)]_1$ fetched by a fixed-table lookup whose cost does not depend on $N$ (Protostar-style) | $\log N$ hashes |
| Open | 1 $\mathbb G_1$ element; the check is deferred into $(P,\Pi)$; 2 pairings in total at the decider | $\log N$ hashes |
| Opening provenance | Supplied by the wallet. aSVC update keys keep it fresh at $O(1)$ per strand update | Computed by the strand-holding node in $O(\log N)$ from its stored tree |
| Recursion backend | HyperNova/ProtoGalaxy + CycleFold on a curve cycle (e.g. BN254/Grumpkin) | Same, **or** a PQ backend: WARP (hash-based, linear-time), LatticeFold+, Neo |

### 3.4 The v2 interface, mapped

- **$\mathsf{Init}$:** every table is $\mathbf 0$ ($\mathsf{Com}=\mathcal O$ / the empty root), $n=0$, registers $\bot$, base proof trivial.
- **$\stackrel{+}{\to}$:** a PCD step with `create` ops. It is additively homomorphic in Variant K: $\mathsf{Com}\mathrel{+}=\sum\delta_iL_i$.
- **$\stackrel{?}{\to}$:** run the PCD decider (plus the pairing check of $(P,\Pi)$ in Variant K). Merge is the arity-$d$ PCD step, and it is valid **iff Φ2 and Φ3 hold**. By I1 this condition is necessary.
- **$\stackrel{v?}{\to}$:** open cell $i$ against a certified $\mathsf{Com}_s$. That is one $\mathbb G_1$ element and 2 pairings, or $\log N$ hashes.
- **Cut-through:** intermediate coins created and spent inside a block never touch the tables. Across blocks, tables hold only live coins. MW-style kernel aggregation is subsumed: signatures are PCD witnesses and never appear in the certificate.

---

## 4. Security

### Assumptions

- **A1 (PCD).** Adaptive knowledge soundness for DAG compliance predicates of polynomial depth.
  - Provable in the AROM for the CCGOS'23 construction.
  - For folding-based PCD: proven in the ROM for constant depth; **heuristic** at polynomial depth, because the FS hash is instantiated in-circuit (I5).
- **A2 (binding).**
  - K: position-binding of KZG under $q$-SDH, plus soundness of batched KZG accumulation in AGM+ROM (BCMS'20).
  - M: collision resistance of Poseidon2.
- **A3.** Collision resistance of $H$ and $\mathsf{enc}$.
- **A4.** EUF-CMA of Schnorr over the embedded curve (DL in the ROM).

### Lemma 1 (Cone consistency)

If every block in $\mathcal C(v)\cup\{v\}$ satisfies Φ1–Φ3, then $\mathcal C(v)$ contains no two distinct blocks at the same position.

*Proof.* Suppose not. Pick an equivocating pair $u_1\ne u_2$ at position $u$ with the latest possible $t_u$. Every position below $u$ is then unique.

**Parent references come from different children.** Parent references are positional and live in hashed state. So $u_1,u_2$ are referenced by the unique blocks at the two *distinct* child positions $c_1=(u_x-1,u_t+1)$ and $c_2=(u_x+1,u_t+1)$; if one child referenced both, they would hash-collide (A3).

Let $m=(u_x,u_t+2)$ be the common child of $c_1$ and $c_2$, and let $j=t_v-u_t-2$.

**Case A: $m\in\mathcal C(v)\cup\{v\}$.** Then Φ2 at $m$ forces $h(u_1)=h(u_2)$. Contradiction.

**Case B: $m\notin\mathcal C(v)\cup\{v\}$.**
- $c_1,c_2\in\mathcal C(v)$ but $m\notin\mathcal C(v)$ means $\operatorname{dist}_W(u_x,x_v)>j$ while $\operatorname{dist}_W(u_x\pm1,x_v)\le j+1$.
- On a line this is impossible. On a circle it forces $u_x=x_v+W/2$ and $j\in\{W/2-2,\,W/2-1\}$.
- Parity ($x+t$ even) gives $j=W/2-2$. So $u=q'(v)$, with $c_1$ on $\lambda(v)$ and $c_2$ on $\rho(v)$.
- Strand states pass unchanged through unique blocks below $u$. So $\mathsf{Reg}_\rho[\lambda(v)]$ arriving at $v$ equals $h(u_2)$, written by $c_2$, and $\mathsf{Reg}_\lambda[\rho(v)]=h(u_1)$, written by $c_1$.
- Φ3 at $v$ then forces $h(u_1)=h(u_2)$. Contradiction. ∎

*In geometric terms:* quads generate every contractible cycle. The single antipodal crossing loop, which goes up $\rho$ and down $\lambda$ for a total lateral span of $W$, generates $H_1(\text{cylinder})=\mathbb Z$. Requiring both checks to agree everywhere is what makes the whole cone consistent.

### Lemma 2 (Exclusivity ⇒ conservation)

On a consistent, Φ-compliant history:
1. Every coin id occupies at most one cell, across all strand tables, on any antichain cut.
2. For every downward-closed region $R$:
$$\sum_{e\ \text{leaving}\ R} n_e = \mu(R)\quad(\text{coins minted in }R).$$

*Proof.*
1. Ids are unique per position (Lemma 1 plus the $\mathit{id}$ format). `create` writes only into empty cells, `spend` empties exactly one cell, and `relocate` moves one cell. By induction along the topological order, each id has at most one cell.
2. Φ4 is a Kirchhoff law at every node: in-flow minus spends plus creates plus mint equals out-flow. Summing over $R$ cancels the internal edges. ∎

### Theorem (SL-PCD soundness)

Let $\mathcal A$ be a PPT adversary that outputs $(v,z_v,\pi_v)$ accepted by the decider (and, in Variant K, the pairing check). Then there is an extractor $\mathcal E$ that outputs a hash-linked history $\mathcal H_v$ rooted at genesis such that, except with probability
$$\varepsilon_{\mathrm{PCD}}+\varepsilon_{\mathrm{bind}}+\varepsilon_{\mathrm{CR}}+q_{\sigma}\,\varepsilon_{\mathrm{sig}},$$
all of the following hold:
1. $\mathcal H_v$ is consistent, and every block in it satisfies Φ.
2. **Exclusivity** and **conservation** hold (Lemma 2).
3. In particular, for every full ring layer $t\le t_v-W/2$ (which lies inside $\mathcal C(v)$), the number of live coins equals the total minted above it.
4. Every spend of an honest key was signed by its holder.
5. Every accepted opening $\stackrel{v?}{\to}$ against $z_v$ names a coin that is live in $\mathcal H_v$ at $v$.

**Completeness.** Honest certificates of $p_L$ and $p_R$ that share a consistent past always merge.

**Corollaries.**
- **Finality = Saros closure.** A block is globally final once some certified block lies $\ge W/2$ layers below it, because that block's cone then covers the full ring.
- **Equivocation is a liveness fault, not a safety fault.** A region with equivocation can never be extended into any certified cone, so it simply stalls until fork choice overtakes it. This is the behaviour the Percolation section asks for, now with a proof.

**Concrete security.** BN254 gives about 100–110 bits after exTNFS. For 128-bit security, use BLS12-381 with non-native emulation (larger constants) or Variant M.

---

## 5. Complexity (per partial node, per block)

$c_\sigma,c_{\mathsf{op}},c_H,c_{\mathsf{fold}}$ are $\mathrm{poly}(\lambda_{\sec})$ constants: Schnorr verification, one deferred KZG claim + lookup (via CycleFold), one Poseidon2 call, and the fold verifier's cost per incoming instance.

| Quantity | Variant K | Variant M |
|---|---|---|
| Step circuit $\lvert F\rvert$ | $d\,c_{\mathsf{fold}}+\lvert X\rvert(c_\sigma+3c_{\mathsf{op}})+O(c_{\mathsf{op}})$ | $d\,c_{\mathsf{fold}}+\lvert X\rvert(c_\sigma+2c_H\log N)+2c_H\log W$ |
| Prover | 1 MSM of size $O(\lvert F\rvert)$ + $O(d\,\lvert F\rvert\log d)$ field ops | same |
| Dependence on $\lvert M\rvert$ / Saros area | **none** | $\log N\ge\log(\lvert M\rvert/W)$, i.e. polylog, optimal by I4 |
| Transit certificate (node → child prover) | $O(1)$ group elements + $O(\lvert F\rvert)$ field elements of folding witness; $O(1)$ if compressed per node | same |
| Light-client certificate | decider proof ($O(1)$ with Groth16, $O(\log\lvert F\rvert)$ Spartan-style) + 2 $\mathbb G_1$ | decider proof |
| Verifier | $O(1)$ pairings | $O(\log\lvert F\rvert)$ |
| Membership opening | 1 $\mathbb G_1$, 2 pairings | $\log N$ hashes |

**Indicative magnitudes** (estimates, not measured): about $10^4$ constraints per op, plus $10^4$–$10^5$ fold overhead per incoming instance. The "Saros area is constant-time for the prover thanks to folding" claim in index.md is therefore **correct**: cost depends on block content and arity, never on the enclosed area.

## 6. Setup and excluded costs

**Setup.**
- Folding: Pedersen/hash-to-curve generators, size $O(\lvert F\rvert)$, transparent.
- Variant K additionally:
  - a KZG SRS with $N$ powers (reuse Perpetual Powers of Tau on BN254; 1-of-$n$ trust);
  - a one-time, publicly re-derivable $O(N\log N)$ computation of $L_i$ and the aSVC update keys.
- A Groth16 decider adds a circuit-specific setup; a Spartan-style decider avoids it.
- $N$ is a hard capacity per strand, so total capacity is $W\cdot N$. Elastic expansion is therefore also a capacity mechanism.

**Excluded costs.** Consensus and fork choice, block propagation, wallet witness maintenance (Variant K: $O(1)$ per update of the coin's own strand), and per-epoch decider compression ($\tilde O(\lvert F\rvert)$, still independent of $\lvert M\rvert$).

## 7. Consequences for `index.md`

1. **Percolation.** Replace the $n^{-1}$ scaling (C2): percolation is the PCD itself. If a summed digest is still wanted, use the inclusion–exclusion form in Appendix A.
2. **Saros / meridian.** The antipodal eclipse is Φ3, and it is *necessary* (Lemma 1, Case B). Finality depth is $W/2$.
3. **Shards:** exactly $W^2/4$ (§1).
4. **Elasticity:** adopt the face-complex rule from §3.2 and the drain-before-retire rule.
5. **Housekeeping:** the image links point to `img/…`, but the files are in the repo root.

---

## Appendix A: a corrected mergeable multiset digest (optional, for audits)

$D(M)=\sum_x m_x\,\mathsf{H2C}(x)$ is ECMH: binding under DL in the ROM, with no sub-exponential generalized-birthday attack in prime-order EC groups, unlike AdHash over $\mathbb Z_n$. The lattice recurrence, valid for depth $<W/2$, is
$$D(v)=D(p_L)+D(p_R)-D(q)+\Delta(v),\qquad n(v)=n(p_L)+n(p_R)-n(q)+\Delta n(v).$$
It gives exact integer multiplicities and correct cut-through. By I1–I3, though, it certifies **neither** exclusivity **nor** well-formedness unless it is computed inside the PCD. Use it only as a cross-check digest.

## References

- Kothapalli, Setty, Tzialla. *Nova*. CRYPTO'22, ePrint 2021/370.
- Kothapalli, Setty. *HyperNova*. ePrint 2023/573.
- Kothapalli, Setty. *CycleFold*. ePrint 2023/1192.
- Eagen, Gabizon. *ProtoGalaxy*. ePrint 2023/1106.
- Bünz, Chen. *Protostar*. ePrint 2023/620.
- Zheng, Gao, Guo, Xiao. *KiloNova: non-uniform PCD from multi-folding*. ePrint 2023/1579.
- Balbás, Nitulescu, Plançon. *Accordion* (batch multi-folding + decider; usable for epoch aggregation, not itself PCD). ePrint 2026/2160.
- Bünz, Chiesa, Mishra, Spooner. *PCD from accumulation schemes*. TCC'20.
- Bünz, Chiesa, Lin, Mishra, Spooner. *PCD without succinct arguments*. CRYPTO'21.
- Chen, Chiesa, Gur, O'Connor, Spooner. *PCD from arithmetized random oracles*. EUROCRYPT'23, ePrint 2023/587.
- Khovratovich, Rothblum, Soukhanov. *How to prove false statements*. ePrint 2025/118.
- Gentry, Wichs. *Separating SNARGs from all falsifiable assumptions*. STOC'11, ePrint 2010/610.
- Tamassia, Triandopoulos. *Computational bounds on hierarchical data processing*. ICALP'05.
- Kate, Zaverucha, Goldberg. *KZG commitments*. ASIACRYPT'10.
- Tomescu et al. *Aggregatable subvector commitments*. SCN'20, ePrint 2020/527.
- Maitin-Shepard, Tibouchi, Aranha. *Elliptic curve multiset hash*. Comput. J. 2017, arXiv 1601.06502.
- Clarke et al. *Incremental multiset hash functions*. ASIACRYPT'03.
- Wagner. *A generalized birthday problem*. CRYPTO'02.
- Boneh, Chen. *LatticeFold+*. CRYPTO'25, ePrint 2025/247.
- Nguyen, Setty. *Neo*. ePrint 2025/294.
- Bünz, Chiesa, Fenzi, Wang. *WARP: linear-time accumulation*. ePrint 2025/753.
- Kim, Barbulescu. *exTNFS*. CRYPTO'16.
