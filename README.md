# Next-order Riesz and Logarithmic Energy on Spheres

For $`d\in\{2,8,24\}`$, let $`\mathbb S^d`$ be the unit sphere in $`\mathbb R^{d+1}`$, with surface area $`A_d`$ and uniform probability measure $`\sigma_d`$. For $`N`$ distinct points, use the **ordered** sum and Euclidean chordal distance:

```math
E_s(X)=\sum_{i\ne j}|x_i-x_j|^{-s}.
```

Write $`\mathcal E_s(d,N)`$ for its infimum when $`0<s<d`$ and its supremum when $`-2<s<0`$. Set

```math
I_{s,d}=\iint_{\mathbb S^d\times\mathbb S^d}|x-y|^{-s}\,d\sigma_d(x)\,d\sigma_d(y).
```

Let $`L_2`$ be the triangular lattice of covolume one, $`L_8=E_8`$, and $`L_{24}`$ the Leech lattice of covolume one. The Epstein convention is

```math
Z_L(s)=\sum_{v\in L\setminus\{0\}}|v|^{-s}
\qquad(\operatorname{Re}s>d),
```

with meromorphic continuation outside the convergence region.

> [!NOTE]
> **Main result (next-order energy).**
>
> Using the lattice Gaussian minorant theorem stated in the manuscript, for each fixed $`-2<s<d`$, $`s\ne0`$,
>
> ```math
> \mathcal E_s(d,N)=I_{s,d}N^2+
> A_d^{-s/d}Z_{L_d}(s)N^{1+s/d}+o(N^{1+s/d}).
> ```
>
> In particular, on the unit sphere $`\mathbb S^8`$,
>
> ```math
> \boxed{\mathcal E_4(8,N)=\frac7{16}N^2-
> \frac{5\sqrt{210}}{48}N^{3/2}+o(N^{3/2}).}
> ```
>
> All limits are over every sufficiently large integer $`N`$.

A proof sketch follows; the [PDF manuscript](PDF/riesz-energy-spheres.pdf) contains the detailed argument for all three dimensions, including positive and negative Riesz exponents, logarithmic energy, and spherical cap discrepancy. Section 4 states the lattice Gaussian minorant theorem and checks its Fourier and covolume conventions. Sections 13–18 give explicit Gaussian error bounds, equal-mass cells, simultaneous selection, and both endpoint estimates.

## Proof sketch

### 1. Transfer sharp Gaussian minorants to the sphere

For every required scale $`\beta`$, the lattice input supplies a Schwartz function satisfying

```math
f_\beta(x)\le e^{-\pi\beta|x|^2},\qquad
\widehat f_\beta\ge0,\qquad
\widehat f_\beta(0)-f_\beta(0)=\Theta_L(\beta)-1.
```

The last equality follows from contact on the lattice, Fourier zeros on the dual lattice, and Poisson summation. Localize these positive definite kernels in small sphere charts. A continuous-background positivity inequality and an approximate-identity limit give, for arbitrary configurations with $`N\to\infty`$,

```math
\liminf_{N\to\infty}\frac1N
\sum_{i,j}e^{-\pi t(N/A_d)^{2/d}|x_i-x_j|^2}\ge\Theta_L(t).
```

The diagonal is included here. No separation, equidistribution, or local lattice structure is assumed for these arbitrary configurations. In dimension eight, Gaussian minorants away from the self-dual scale suffice; nearby scales and continuity of theta recover the desired profile.

### 2. Subtract the actual background before taking the Mellin limit

Put $`a_N=(N/A_d)^{1/d}`$ and let $`B_d(u)`$ be the Gaussian potential of the uniform probability measure with kernel $`e^{-\pi u|x-y|^2}`$. If $`G_N`$ is the normalized full Gaussian sum above, define

```math
H_N(t)=G_N(t)-NB_d(a_N^2t),\qquad F_N(t)=H_N(t)-1.
```

Gaussian positivity gives $`H_N\ge0`$, while polar integration gives

```math
NB_d(a_N^2t)\le t^{-d/2},\qquad
NB_d(a_N^2t)\longrightarrow t^{-d/2}.
```

Thus $`F_N(t)\ge-\min(1,t^{-d/2})`$. For $`0<s<d`$ this is an integrable lower bound after multiplication by $`t^{s/2-1}`$. The Mellin identity and Fatou's lemma give the sharp universal lower bound with coefficient $`A_d^{-s/d}Z_L(s)`$.

For $`-2<s<0`$, the subtracted Mellin formula uses $`H_N`$ and has a negative gamma prefactor. The same Gaussian argument gives the universal upper bound appropriate to a maximization problem.

### 3. Build matching configurations in exact-area charts

The explicit chart

```math
\Phi(z,t)=\bigl(z,\sqrt{1-|z|^2}\sin t,\sqrt{1-|z|^2}\cos t\bigr)
```

has Gram determinant one. Small lattice patches therefore have exact surface-area masses. A finite separated family can cover arbitrarily close to the whole sphere, with masses chosen as rational $`d`$th powers so that node counts and background masses agree exactly.

For $`d=8`$, $`s=4`$, a sixth-order equal-weight boundary rule yields a curved-background quadrature error $`O(h^5)`$. Simultaneous differentiation moves the most singular terms to faces, where the Peano kernel controls them. Every interior row has the local regularized lattice limit, and all boundary rows have a common $`O(h^4)`$ bound. Neutralization then produces the coefficient $`Z_{E_8}(4)=-5\pi^2/6`$.

For the general construction, the order-fourteen rule bounds the physical Gaussian bump error by a constant times the softened Gaussian integral over the sphere. Its squared integral is computed exactly. If $`H_{F,N}`$ is the centered foreground Gaussian defect divided by $`N`$, the resulting bound is

```math
\int_0^w\alpha^{q-1}H_{F,N}(\alpha)\,d\alpha
\le \frac{Cw^{q+14-d/2}}{q+14-d/2}
   +C_{F,q}a_N^{d-28-2q},\qquad -1<q<0.
```

The second term tends to zero in all three dimensions. The manuscript also gives the critical order-twelve calculation in dimension 24: for $`q=s/2>0`$, its smallest-scale error is $`O(N^{-s/24})`$.

### 4. Construct one configuration at every integer size

For fixed patch sides $`\lambda_i`$, set

```math
n_i(N)=\lfloor\lambda_i a_N\rfloor,\qquad
\lambda_i(N)=\frac{n_i(N)}{a_N}.
```

The contracted patch has exactly $`n_i(N)^d`$ nodes and probability mass $`n_i(N)^d/N`$. Fill its complement with exactly

```math
k_N=N-\sum_i n_i(N)^d
```

points, one from each cell of mass $`1/N`$. In dimensions eight and 24, a fine chart grid and a coarser partition of the remaining mass give the squared-diameter bound, including the cost of cells that join distant pieces. In dimension two, a spanning tree of adjacent cells keeps each carried remainder inside one original cell and gives a uniform diameter bound.

Three nonnegative costs are controlled together: the small-scale centered Gaussian integral, the residual Gaussian sum at the left edge of the window, and the large-scale off-diagonal integral. Their expectations are bounded explicitly. Markov's inequality and the union bound select **one** injective configuration satisfying all three estimates.

A diagonal choice of the approximation stage gives configurations at every sufficiently large integer $`N`$ with the sharp Gaussian profile and uniform bounds

```math
\int_0^1\alpha^{q-1}H_N(\alpha)\,d\alpha\le\mathcal B_0,
\qquad
\int_1^\infty\alpha^{v-1}(G_N(\alpha)-1)\,d\alpha\le\mathcal B_\infty,
```

where $`-1<q<0<v<d/2`$. For a Riesz exponent $`s=2p`$, choose $`q<p<v`$. The two omitted tails then tend to zero by explicit power estimates. The same construction covers dimension two; its pointwise small-scale bound and its shrinking-cutoff integral are proved separately in Section 17.

### 5. Derive logarithmic energy and cap discrepancy

A Frullani identity, with separate small- and large-scale bounds, establishes

```math
\mathcal E_{\log}(d,N)=W_dN^2-\frac Nd\log N+
\left(Z'_{L_d}(0)+\frac1d\log A_d\right)N+o(N),
```

where $`W_d=\iint-\log|x-y|\,d\sigma_d(x)d\sigma_d(y)`$. The same two integral bounds control both ends of the Frullani integral on the same configurations. No differentiation of an asymptotic remainder is used.

For cap discrepancy, integrate cap height against $`dt`$ on $`[-1,1]`$ and direction against $`\sigma_d`$. Stolarsky's identity gives

```math
D_2(X)^2=\kappa_d\left(I_{-1,d}-\frac{E_{-1}(X)}{N^2}\right),
\qquad
\kappa_d=\frac{\Gamma((d+1)/2)}{d\sqrt\pi\,\Gamma(d/2)}.
```

Consequently,

```math
N^{1/2+1/(2d)}\inf_XD_2(X)\longrightarrow
\sqrt{-\kappa_d A_d^{1/d}Z_{L_d}(-1)}.
```

## Detailed manuscript

- [PDF manuscript](PDF/riesz-energy-spheres.pdf)

## Conclusion

Using the lattice Gaussian minorant theorem stated in the manuscript, the argument gives the next-order Riesz and logarithmic energy asymptotics on the unit spheres of dimensions two, eight, and 24. Localized Gaussian bounds and matching lattice-patch constructions give the same coefficient. Adjusting each patch side to the prescribed density gives every integer size, and one simultaneous selection controls both endpoints. Stolarsky's identity gives the corresponding spherical cap discrepancy limit.

In dimension eight, the inverse-fourth coefficient is explicit:

```math
\mathcal E_4(8,N)=\frac7{16}N^2-
\frac{5\sqrt{210}}{48}N^{3/2}+o(N^{3/2}).
```

All energies use ordered pairs and chordal distance. Negative Riesz exponents use a supremum; positive Riesz and logarithmic energies use an infimum.
