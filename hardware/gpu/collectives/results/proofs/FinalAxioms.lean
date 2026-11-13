import Obend.Hardware.Gpu.NttKernel
import Obend.Hardware.Gpu.CollectiveBuildCorrect
import Obend.Hardware.Gpu.CollectiveWorkBuild
import Obend.Hardware.Gpu.ArrayEmitCorrect
#print axioms Obend.Hardware.Gpu.Ntt.nttBlockProgram_dft
#print axioms Obend.Hardware.Gpu.NttSource.source_to_gpu_dft_encoded
#print axioms Obend.Hardware.Gpu.GoldilocksSourceCorrect.glMul_sound
#print axioms Obend.Hardware.Gpu.BlockPlan.Plan.source_to_gpu_encoded
#print axioms Obend.Hardware.Gpu.BlockPlan.Plan.not_racy
#print axioms Obend.Hardware.Gpu.CollectiveBuildCorrect.build_initialMemory_value
#print axioms Obend.Hardware.Gpu.CollectiveWorkBuild.build_work
#print axioms Obend.Hardware.Gpu.ArrayEmitCorrect.compile_runProgram
