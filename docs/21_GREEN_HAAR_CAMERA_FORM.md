# Form-first Green/Haar camera interface

## Closed abstract mechanism

Let `CameraFinsupp` be the finitely supported all-bases camera core equipped
with its intrinsic Gram norm, and let `CameraHilbert` be its completion.  The
new module proves that every bounded real core functional

```text
q : CameraFinsupp →L[ℝ] ℝ
```

has a unique continuous extension

```text
extendCameraCoreFunctional q : CameraHilbert →L[ℝ] ℝ.
```

The extension agrees with `q` on the canonical dense embedding and satisfies

```math
\left\|\mathrm{extend}(q)\right\|=\lVert q\rVert.
```

Thus a source-dependent bilinear formula can use this result after its camera
variable has been bundled as a bounded core functional.  The theorem does not
establish that boundedness for a proposed research formula.

More generally, the same construction is proved for every real-linear core
map into a complete real normed target.  Taking that target to be the native
two-coordinate real plane retains the whole readout.  The C3 crosswalk already
proves that its notation in `ℂ` is the inverse-coordinate packaging through
`Complex.equivRealProdCLM`; it is not a different operator or a new channel.

## Uniform atlas restrictions

For every real linear isometric inclusion

```text
i : A →ₗᵢ[ℝ] CameraHilbert,
```

the restricted functional obeys

```math
\left|\mathrm{extend}(q)(i u)\right|
\le \lVert q\rVert\,\lVert u\rVert.
```

The constant contains neither the cardinality of the atlas nor a cutoff.  For
the concrete finite-label camera subspaces, the restrictions are exactly
compatible under enlargement.

## Canonical Naimark target

For `g : NaimarkSpace`, the canonical target is

```math
q_g(u)=\langle g,V u\rangle,
```

where `V` is the existing Naimark isometry.  Lean proves that this is the
unique extension of the corresponding core pairing and that

```math
|q_g(u)|\le \lVert g\rVert\,\lVert u\rVert.
```

A unit source therefore gives the atlas-independent constant one.

## Remaining research gate

This module does not define a Green/Haar source or its arithmetic core
functional.  The next independent obligation is to define that functional on
`CameraFinsupp` and prove one intrinsic Gram estimate

```math
|q(u)|\le C\lVert u\rVert
```

with `C` independent of every finite prime atlas.  Only then does the generic
extension apply.  A bounded vector-valued camera synthesis, a Green closing
statement, and any conclusion about zeros remain outside this result.
