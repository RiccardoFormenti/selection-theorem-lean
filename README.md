Project description

This repository is a Lean 4 formalization of two classical selection results for lower hemicontinuous set-valued maps. The project develops basic definitions for correspondences and lower hemicontinuity, proves an approximate selection theorem for lower hemicontinuous correspondences with nonempty convex values into a normed space, and then builds on that result to formalize Michael’s selection theorem.

The code is organized in three main files. Correspondences.lean introduces the basic language of set-valued maps and lower hemicontinuity. ApproximateSelection.lean proves the existence of continuous approximate selections using partitions of unity. MichaelSelection.lean refines this construction through an iterative argument, producing a genuine continuous selection for lower hemicontinuous correspondences with nonempty closed convex values in a complete separable normed space.

