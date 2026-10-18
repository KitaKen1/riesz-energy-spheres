import Riesz.Definitions
import Riesz.Asymptotics
import Riesz.Boundary
import Riesz.Quadrature
import Riesz.GaussianMellin
import Riesz.CharFun
import Riesz.GaussianPSD
import Riesz.FiniteBackground
import Riesz.QuadratureError
import Riesz.PeanoKernel
import Riesz.PeanoInterior
import Riesz.PeanoRemainder
import Riesz.SmoothQuadrature
import Riesz.CellQuadrature
import Riesz.LocalQuadrature
import Riesz.LocalCellQuadrature
import Riesz.TensorQuadrature
import Riesz.CubeQuadrature
import Riesz.CubeNodes
import Riesz.BoxQuadrature
import Riesz.L1Quadrature
import Riesz.QuadraticKernel
import Riesz.FlatKernel
import Riesz.FarCell
import Riesz.DyadicShell
import Riesz.NodeCounting
import Riesz.LocalizedQuadrature
import Riesz.AnnularCutoff
import Riesz.AnnularQuadrature
import Riesz.AnnularPartition
import Riesz.E8Coordinates
import Riesz.ObliqueAnnulus
import Riesz.ObliquePartition
import Riesz.E8Volume
import Riesz.CubeLebesgue
import Riesz.E8FarPhysical
import Riesz.NodeSeparation
import Riesz.E8Grid
import Riesz.E8Parity
import Riesz.E8Separation
import Riesz.E8NearNodes
import Riesz.E8NearIntegral
import Riesz.E8NearQuadrature
import Riesz.E8FlatRow
import Riesz.E8FlatPhysicalRow
import Riesz.PeanoEndpoint
import Riesz.PeanoSingularWeight
import Riesz.E8PotentialApprox
import Riesz.GlobalRows
import Riesz.SphereMeasure8
import Riesz.SphereArea8
import Riesz.SphereBall8
import Riesz.SphereIntegrable8
import Riesz.SphereValue8
import Riesz.E8Theta
import Riesz.E8ThetaAnalytic
import Riesz.E8Dual
import Riesz.WeightFour
import Riesz.ZetaValue

import Riesz.E8QExpansion
import Riesz.E8Covolume
import Riesz.E8ThetaFourier
import Riesz.E8ThetaModular
import Riesz.E8Dirichlet
import Riesz.E8Shells
import Riesz.E8Epstein
import Riesz.E8SmoothValue
import Riesz.E8HeatBackground

import Riesz.E8HeatCellComparison

import Riesz.GaussianDerivativeCertificate

import Riesz.E8DampedQuadrature

import Riesz.E8CellLimit

import Riesz.E8CenteredFullRow
import Riesz.E8InteriorFullRow
import Riesz.E8FullRowMean
import Riesz.QuadraticFace
import Riesz.FaceIntegral
import Riesz.SingularQuadrature
import Riesz.E8PotentialRegularity
import Riesz.MovingInterval
import Riesz.E8MovingFaces
import Riesz.E8PotentialAveraging
import Riesz.E8NearPotentialMean
import Riesz.E8FlatBackgroundLimit
import Riesz.CurvedNearComparison
import Riesz.E8SphereGraph
import Riesz.E8SphereGraphEnergy
import Riesz.EqualAreaChart8
import Riesz.EqualAreaGram8
import Riesz.EqualAreaCone8
import Riesz.EqualAreaConeDerivative8
import Riesz.EqualAreaConeJacobian8
import Riesz.EqualAreaMeasure8
import Riesz.EqualAreaRescaling8
import Riesz.EqualAreaRescalingLimit8
import Riesz.EqualAreaRescalingGeometry8
import Riesz.EqualAreaNearBackground8
import Riesz.EqualAreaMovingRescaling8
import Riesz.EqualAreaMovingBounds8
import Riesz.EqualAreaPatchClass8
import Riesz.EqualAreaPatchNear8
import Riesz.CurvedAnnularRegularization8
import Riesz.CurvedAnnularComposition8
import Riesz.CurvedAnnularQuadrature8
import Riesz.EqualAreaPatchAnnular8
import Riesz.EqualAreaPatchFar8

import Riesz.CurvedFarPotential8
import Riesz.CurvedBackground8
import Riesz.EqualAreaPatchBackground8

import Riesz.CurvedNearQuadrature8

import Riesz.CurvedFullRow8

import Riesz.EqualAreaPatchRow8

import Riesz.EqualAreaPatchNeutralized8

import Riesz.EqualAreaPatchEnergy8

import Riesz.EqualAreaAffine8

import Riesz.EqualAreaPatchMeasure8

import Riesz.EqualAreaFinitePatchMass8

import Riesz.EqualAreaPatchTransport8

import Riesz.EqualAreaPatchRieszTransport8

import Riesz.EqualAreaFinitePatchGeometry8

import Riesz.SphereFiniteCompactCores8

import Riesz.EqualAreaInverse8

import Riesz.SphereSmallChartCores8

import Riesz.EqualAreaCoordinateBuffers8

import Riesz.CompactGrid8

import Riesz.GridShrink8

import Riesz.SphereGrid8

import Riesz.SphereGridMass8

import Riesz.SphereShrunkGrid8

import Riesz.CappedSphereGrid8

import Riesz.AffineGridCube8

import Riesz.RationalScale8

import Riesz.RationalNodeBudget8

import Riesz.RationalCubeFamily8

import Riesz.RationalResidualBudget8

import Riesz.CrossPatchKernel8

import Riesz.CrossPatchQuadrature8

import Riesz.CrossPatchBlock8

import Riesz.CrossPatchPhysical8

import Riesz.CrossPatchFamily8

import Riesz.SphereAtomless8

import Riesz.ResidualFirstMoment

import Riesz.SphereResidual8

import Riesz.RationalResidualPoints8

import Riesz.SphereBackgroundSplit8

import Riesz.SphereResidualAssembly8

import Riesz.RationalResidualEnergy8

import Riesz.SphereFiniteFamilyAssembly4

import Riesz.SmallE8PhysicalAssembly4

import Riesz.SphereSharpUpperSubsequence8

import Riesz.SphereEnergySubconfiguration4

import Riesz.RationalSizeCeiling8

import Riesz.SphereSharpUpperAllN8

import Riesz.GaussianMeasurePSD

import Riesz.DiffuseGaussianBackground

import Riesz.SphereGaussianBackground8

import Riesz.SphereGaussianCommonLower8

import Riesz.SphereGaussianBall8

import Riesz.SphereGaussianPolar8

import Riesz.SphereGaussianPolynomial8

import Riesz.SphereGaussianMajorant8

import Riesz.SphereGaussianMellinBackground8

import Riesz.SphereGaussianMellinEnergy8

import Riesz.SphereGaussianMellinScale8

import Riesz.RealFatouTruncation

import Riesz.E8GaussianRealProfile8

import Riesz.SphereGaussianProfileLowerBridge8

import Riesz.SpectralMeasurePSD

import Riesz.SchwartzMeasurePSD

import Riesz.LocalizedSchwartzPSD

import Riesz.SphereLocalizedSchwartzPSD8

import Riesz.CompactKernelCorrelation

import Riesz.CompactSchwartzBackground

import Riesz.SupportedChartCutoff8

import Riesz.EqualAreaEuclideanGeometry8

import Riesz.EqualAreaEuclideanTransport8

import Riesz.SphereChartSchwartzBackground8

import Riesz.FiniteCutoffSquarePartition

import Riesz.SphereCutoffPartition8

import Riesz.CompactUniformApproximateIdentity

import Riesz.SpherePartitionCoordinateProfiles8

import Riesz.SpherePartitionUniformRows8

import Riesz.SpherePartitionDensityRows8

import Riesz.SpherePartitionSchwartzPSD8

import Riesz.SpherePartitionGaussianComparison8

import Riesz.SphereGaussianSchwartzProfile8

import Riesz.E8GaussianContact8

import Riesz.GaussianMellinGeneral

import Riesz.E8CKMRVContract8

import Riesz.SphereRieszMellinRpow8

import Riesz.SphereRieszLowerRpow8

import Riesz.E8EpsteinStrip8

import Riesz.SphereRieszConstPair8

import Riesz.E8EpsteinTwo8

import Riesz.SphereGaussianMonotone8

import Riesz.SphereRieszUpperRpow8

import Riesz.SphereRieszTransfer8

import Riesz.SphereRieszShortRange8

import Riesz.ResidualJointSelection

import Riesz.SphereShortRangeKernel8

import Riesz.SphereShortRangeResidual8

import Riesz.SphereShortRangeTail8

import Riesz.SphereShortRangeSeparated8

import Riesz.RationalPatchSeparation8

import Riesz.RationalJointResidual8

import Riesz.SphereJointUpperSubsequence8

import Riesz.SphereRieszUpperFourLt8

import Riesz.SphereRieszUpperFourLtAllN8

import Riesz.SphereRieszSharpFourLt8

import Riesz.AmbientBumpSquare9

import Riesz.GaussianCompositionSixth

import Riesz.CubeEnvelopeQuadrature

import Riesz.GaussianOneDimBounds

import Riesz.NormalizedBumpError

import Riesz.SmallPatchBumpError8

import Riesz.PatchGaussianDefect8

import Riesz.SphereBoundedKernelAssembly8

import Riesz.SphereLongRangeKernel8

import Riesz.SphereLongRangeBlock8

import Riesz.GaussianBlockBounds8

import Riesz.PatchLongRangeBound8

import Riesz.RationalLongRangeResidual8

import Riesz.SphereLongRangeSubsequence8

import Riesz.SphereMassSplitAssembly8

import Riesz.LongRangeRescale8

import Riesz.RationalSizeFloor8

import Riesz.SphereLongRangeAllN8

import Riesz.SphereRieszUpperLtFour8

import Riesz.GammaNegStrip

import Riesz.SphereRieszNegMellin8

import Riesz.E8EpsteinNeg8

import Riesz.SphereRieszNegUpper8

import Riesz.SphereStolarsky8

import Riesz.SphereCapDiscrepancy8

import Riesz.SphereAbsMoment8

import Riesz.SphereRieszNegTransfer8

import Riesz.SphereLogEnergy8

import Riesz.SphereLogLower8

import Riesz.SphereLogCoefficient8

import Riesz.SphereLogConstPair8

import Riesz.CellFirstMoment

import Riesz.ExactMassCut

import Riesz.SphereCapDiscrepancySqrt8

import Riesz.SphereNegMacroKernel8

import Riesz.SphereNegMacroBlock8

import Riesz.GaussianCompositionSixthSmall

import Riesz.NormalizedBumpErrorSmall

import Riesz.SmallPatchBumpErrorSmall8

import Riesz.PatchGaussianDefectSmall8

import Riesz.PatchNegMacroBound8

import Riesz.NegMacroStratified8

import Riesz.GaussianBlockUnion8

import Riesz.StratifiedResidualEnergy

import Riesz.NegJointResidual8

import Riesz.RationalNegJoint8

import Riesz.ExactMassSlices

import Riesz.PrescribedMassSlices

import Riesz.NegMacroEndBounds8

import Riesz.RationalNegJointCutoff8

import Riesz.NegSharpSubsequence8

import Riesz.NegMassSplit8

import Riesz.NegAllN8

import Riesz.SphereCapDiscrepancyUpper8

import Riesz.SphereLogUpper8

import Riesz.CarryOverSlices

import Riesz.SphereGridPool8

import Riesz.SphereChartBiLip8

import Riesz.ChartGridBoxes8

import Riesz.ChartBoundaryMinkowski8

import Riesz.SphereChartRegions8

import Riesz.SphereChartPool8

import Riesz.SphereStratification8

import Riesz.PatchBoundaryMinkowski8

import Riesz.ResidualStratification8

import Riesz.SphereMeasureD

import Riesz.EqualAreaChartD

import Riesz.EqualAreaGramD

import Riesz.EqualAreaConeD

import Riesz.EqualAreaConeDerivativeD

import Riesz.EqualAreaConeJacobianD

import Riesz.EqualAreaMeasureD

import Riesz.EqualAreaInverseD

import Riesz.LeechLattice24

import Riesz.LeechDual24

import Riesz.LeechTheta24

import Riesz.PatchSupportD

import Riesz.EqualAreaRescaling24

import Riesz.EqualAreaRescalingLimit24

import Riesz.EqualAreaRescalingGeometry24

import Riesz.EqualAreaMovingRescaling24

import Riesz.EqualAreaMovingBounds24

import Riesz.EqualAreaPatchClass24

import Riesz.EqualAreaAffine24

import Riesz.EqualAreaPatchMeasure24

import Riesz.EqualAreaPatchTransport24

import Riesz.EqualAreaFinitePatchGeometry24

import Riesz.EqualAreaFinitePatchMass24

import Riesz.EqualAreaCoordinateBuffers24

import Riesz.LeechGaussianContact24

import Riesz.LeechProfileLower24

import Riesz.LeechRegularized24

import Riesz.SphereBallD

import Riesz.SphereGaussianBackground24









import Riesz.SphereRieszLower24

import Riesz.SphereGaussianUpper24

import Riesz.LeechGaussianEnds24

import Riesz.LeechGaussianBudget24

import Riesz.BoundaryTwelveNodes

import Riesz.BoundaryTwelveMoments

import Riesz.BoundaryTwelveQuadrature

import Riesz.BoundaryTwelvePeano

import Riesz.BoundaryTwelveLocalError

import Riesz.BoundaryTwelveL1Error

import Riesz.BoundaryTwelveTensor

import Riesz.BoundaryTwelveNodeGeometry

import Riesz.BoundaryTwelveLocalizedError

import Riesz.BoundaryTwelveEnvelope

import Riesz.AmbientBumpSquare25

import Riesz.EqualAreaMovingHigherBounds24

import Riesz.LeechTwelfthSmallBudget24

import Riesz.LeechTwelfthGaussianBudget24

import Riesz.GaussianCompositionTwelfth

import Riesz.GaussianOneDimTwelve

import Riesz.NormalizedBumpError24

import Riesz.SmallPatchBumpError24

import Riesz.LeechForegroundBump24

import Riesz.LeechForegroundDefect24

import Riesz.SmallBudgetKernel24

import Riesz.StratifiedJointSelection

import Riesz.LeechForegroundBudget24

import Riesz.LeechJointResidual24

import Riesz.LeechCommonBudget24

import Riesz.LeechForegroundTail24

import Riesz.LeechWindowReduction24

import Riesz.SphereResidualCells24

import Riesz.SphereRationalFamily24

import Riesz.LeechForegroundWindow24

import Riesz.RationalSizeCeiling24

import Riesz.LeechEpstein24

import Riesz.LeechSharpUpper24

import Riesz.BoundaryFourteen

import Riesz.GaussianCompositionFourteenth

import Riesz.LeechFourteenth24

import Riesz.SphereRieszNeg24

import Riesz.LeechNegBlock24

import Riesz.SphereStratification24

import Riesz.LeechNegSharp24

import Riesz.SphereCapDiscrepancy24

import Riesz.SphereLog24

import Riesz.LeechLogBlock24

import Riesz.SphereLogUpper24

import Riesz.HexLattice2

import Riesz.EqualAreaHex2

import Riesz.HexProfileLower2

import Riesz.SphereRieszLower2

import Riesz.HexGaussianEnds2

import Riesz.HexGaussianBridge2

import Riesz.SphereRieszLowerMain2

import Riesz.HexConstruction2

import Riesz.SphereCellConstruction2

import Riesz.SphereStratification2

import Riesz.HexNegSharp2

import Riesz.SphereLog2

import Riesz.HexLogConstruction2

import Riesz.SphereCapDiscrepancy2

import Riesz.OptimalSphereEnergy

import Riesz.E8SchwartzInputOff8

import Riesz.E8InputFromCertificate8

import Riesz.SphereProfileFinal8

import Riesz.E8KernelBridge8

import Riesz.SphereMain8

import Riesz.SphereStatements8

import Riesz.SphereMain24
import Riesz.SphereOptimalMain24
