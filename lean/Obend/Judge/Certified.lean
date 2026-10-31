module
/-
# Obend.Judge.Certified — a conditional identity proved through a real solver's LRAT certificate

`noCarry 8` (`Obend.Judge.Identity`): for 8-bit `x` and `y` with `x &&& y = 0`, the ripple-carry sum
`x + y` with its carry out is `x ||| y` with a zero top bit. `encode (noCarry 8)` (231 variables, 683
clauses) was written as DIMACS (`lean/tests/judge/nocarry8.cnf`), refuted by CaDiCaL 3.0.1
(`cadical --lrat --binary=false`), and its LRAT proof (`lean/tests/judge/nocarry8.lrat`, 215 steps)
is the literal `steps8` below. The kernel runs the checker on it (`steps8_accepted`, `decide +kernel`):
the trust base is the Lean kernel. `noCarry8_holds` is the identity, through `Translation.sound`.

The tooth: the same proof with one clause deleted right after it is added (step `687`, which the
addition of `688` cites) is refused by `missingHint 687` at that step (index 10) (`dropped_refused`). The
32-bit instance (`nocarry32.*`, 3207 steps) is checked by the compiled checker on its bytes
(`obend lrat`; trust `compiled`), not here.
-/
public import Obend.Judge.Identity

public section
namespace Obend.Judge.Certified
open Obend.Judge.Lrat Obend.Judge.Identity
set_option autoImplicit false

set_option maxRecDepth 100000

/-- CaDiCaL's LRAT refutation of `encode (noCarry 8)`, step for step. -/
def steps8 : List Step := [
    
.del [5],
    .add 684 [19, 18] [1, 7],
    .del [7],
    .add 685 [-36, 34] [54, 55],
    .del [55, 56],
    .add 686 [36, -34] [54, 57],
    .del [57, 58],
    .add 687 [-43] [73, 78],
    .del [78, 79, 80, 82],
    .add 688 [-44, 40] [687, 83],
    .del [83],
    .add 689 [-53] [105, 110],
    .del [110, 111, 112, 114],
    .add 690 [-54, 50] [689, 115],
    .del [115],
    .add 691 [-67] [150, 155],
    .del [155, 156, 157, 159],
    .add 692 [-68, 64] [691, 160],
    .del [160],
    .add 693 [-85] [208, 213],
    .del [213, 214, 215, 217],
    .add 694 [-86, 82] [693, 218],
    .del [218],
    .add 695 [-107] [279, 284],
    .del [284, 285, 286, 288],
    .add 696 [-108, 104] [695, 289],
    .del [289],
    .add 697 [-133] [363, 368],
    .del [368, 369, 370, 372],
    .add 698 [-134, 130] [697, 373],
    .del [373],
    .add 699 [-163] [460, 465],
    .del [465, 466, 467, 469],
    .add 700 [-164, 160] [699, 470],
    .del [470],
    .add 701 [-196] [566, 571],
    .del [571, 572, 573, 575],
    .add 702 [-197, 193] [701, 576],
    .del [576],
    .add 703 [-220, 218] [647, 648],
    .del [648, 649],
    .add 704 [220, -218] [647, 650],
    .del [650, 651, 654],
    .add 705 [-222, 220] [652, 655],
    .del [655],
    .add 706 [33] [683, 680],
    .add 707 [230] [683, 681],
    .add 708 [31] [706, 47],
    .add 709 [-32] [706, 48],
    .add 710 [29] [708, 41],
    .add 711 [-30] [708, 42],
    .add 712 [27] [710, 35],
    .add 713 [-28] [710, 36],
    .add 714 [25] [712, 29],
    .add 715 [-26] [712, 30],
    .add 716 [23] [714, 23],
    .add 717 [-24] [714, 24],
    .add 718 [21] [716, 17],
    .add 719 [-22] [716, 18],
    .add 720 [19] [718, 11],
    .add 721 [-20] [718, 12],
    .add 722 [-18] [720, 6],
    .add 723 [-193] [722, 563, 564, 4],
    .add 724 [-197] [723, 702],
    .add 725 [-199] [724, 581],
    .add 726 [-192] [721, 560, 561, 10],
    .add 727 [-200] [726, 725, 586],
    .add 728 [-202] [727, 591],
    .add 729 [-191] [719, 557, 558, 16],
    .add 730 [-203] [729, 728, 596],
    .add 731 [-205] [730, 601],
    .add 732 [-190] [717, 554, 555, 22],
    .add 733 [-206] [732, 731, 606],
    .add 734 [-208] [733, 611],
    .add 735 [-189] [715, 551, 552, 28],
    .add 736 [-209] [735, 734, 616],
    .add 737 [-211] [736, 621],
    .add 738 [-188] [713, 548, 549, 34],
    .add 739 [-212] [738, 737, 626],
    .add 740 [-214] [739, 631],
    .add 741 [-187] [711, 545, 546, 40],
    .add 742 [-215] [741, 740, 636],
    .add 743 [-217] [742, 641],
    .add 744 [-186] [709, 542, 543, 46],
    .add 745 [-218] [744, 743, 646],
    .add 746 [-220] [745, 703],
    .add 747 [-222] [746, 705],
    .add 748 [-160] [722, 457, 458, 4],
    .add 749 [-164] [748, 700],
    .add 750 [-166] [749, 475],
    .add 751 [-159] [721, 454, 455, 10],
    .add 752 [-167] [751, 750, 480],
    .add 753 [-169] [752, 485],
    .add 754 [-158] [719, 451, 452, 16],
    .add 755 [-170] [754, 753, 490],
    .add 756 [-172] [755, 495],
    .add 757 [-157] [717, 448, 449, 22],
    .add 758 [-173] [757, 756, 500],
    .add 759 [-175] [758, 505],
    .add 760 [-156] [715, 445, 446, 28],
    .add 761 [-176] [760, 759, 510],
    .add 762 [-178] [761, 515],
    .add 763 [-155] [713, 442, 443, 34],
    .add 764 [-179] [763, 762, 520],
    .add 765 [-181] [764, 525],
    .add 766 [-154] [711, 439, 440, 40],
    .add 767 [-182] [766, 765, 530],
    .add 768 [-130] [722, 360, 361, 4],
    .add 769 [-134] [768, 698],
    .add 770 [-136] [769, 378],
    .add 771 [-129] [721, 357, 358, 10],
    .add 772 [-137] [771, 770, 383],
    .add 773 [-139] [772, 388],
    .add 774 [-128] [719, 354, 355, 16],
    .add 775 [-140] [774, 773, 393],
    .add 776 [-142] [775, 398],
    .add 777 [-127] [717, 351, 352, 22],
    .add 778 [-143] [777, 776, 403],
    .add 779 [-145] [778, 408],
    .add 780 [-126] [715, 348, 349, 28],
    .add 781 [-146] [780, 779, 413],
    .add 782 [-148] [781, 418],
    .add 783 [-125] [713, 345, 346, 34],
    .add 784 [-149] [783, 782, 423],
    .add 785 [-104] [722, 276, 277, 4],
    .add 786 [-108] [785, 696],
    .add 787 [-110] [786, 294],
    .add 788 [-103] [721, 273, 274, 10],
    .add 789 [-111] [788, 787, 299],
    .add 790 [-113] [789, 304],
    .add 791 [-102] [719, 270, 271, 16],
    .add 792 [-114] [791, 790, 309],
    .add 793 [-116] [792, 314],
    .add 794 [-101] [717, 267, 268, 22],
    .add 795 [-117] [794, 793, 319],
    .add 796 [-119] [795, 324],
    .add 797 [-100] [715, 264, 265, 28],
    .add 798 [-120] [797, 796, 329],
    .add 799 [-82] [722, 205, 206, 4],
    .add 800 [-86] [799, 694],
    .add 801 [-88] [800, 223],
    .add 802 [-81] [721, 202, 203, 10],
    .add 803 [-89] [802, 801, 228],
    .add 804 [-91] [803, 233],
    .add 805 [-80] [719, 199, 200, 16],
    .add 806 [-92] [805, 804, 238],
    .add 807 [-94] [806, 243],
    .add 808 [-79] [717, 196, 197, 22],
    .add 809 [-95] [808, 807, 248],
    .add 810 [-64] [722, 147, 148, 4],
    .add 811 [-68] [810, 692],
    .add 812 [-70] [811, 165],
    .add 813 [-63] [721, 144, 145, 10],
    .add 814 [-71] [813, 812, 170],
    .add 815 [-73] [814, 175],
    .add 816 [-62] [719, 141, 142, 16],
    .add 817 [-74] [816, 815, 180],
    .add 818 [-50] [722, 102, 103, 4],
    .add 819 [-54] [818, 690],
    .add 820 [-56] [819, 120],
    .add 821 [-49] [721, 99, 100, 10],
    .add 822 [-57] [821, 820, 125],
    .add 823 [-40] [722, 70, 71, 4],
    .add 824 [-44] [823, 688],
    .add 825 [-16, 153] [709, 46, 438],
    .add 826 [-184, -185] [767, 539, 533, 825, 537, 437],
    .del [539],
    .add 827 [-185] [767, 826, 535, 536, 538, 435, 531],
    .add 828 [-223] [827, 747, 658],
    .add 829 [-15, 124] [711, 40, 344],
    .add 830 [-151, -152] [784, 432, 426, 829, 430, 343],
    .del [432],
    .add 831 [-152] [784, 830, 428, 429, 431, 341, 424],
    .add 832 [-224] [831, 828, 661],
    .add 833 [-14, 99] [713, 34, 263],
    .add 834 [-122, -123] [798, 338, 332, 833, 336, 262],
    .del [338],
    .add 835 [-123] [798, 834, 334, 335, 337, 260, 330],
    .add 836 [-225] [835, 832, 664],
    .add 837 [-13, 78] [715, 28, 195],
    .add 838 [-97, -98] [809, 257, 251, 837, 255, 194],
    .del [257],
    .add 839 [-98] [809, 838, 253, 254, 256, 192, 249],
    .add 840 [-226] [839, 836, 667],
    .add 841 [-12, 61] [717, 22, 140],
    .add 842 [-76, -77] [817, 189, 183, 841, 187, 139],
    .del [189],
    .add 843 [-77] [817, 842, 185, 186, 188, 137, 181],
    .add 844 [-227] [843, 840, 670],
    .add 845 [-11, 48] [719, 16, 98],
    .add 846 [-59, -60] [822, 134, 128, 845, 132, 97],
    .del [134],
    .add 847 [-60] [822, 846, 130, 131, 133, 95, 126],
    .add 848 [-228] [847, 844, 673],
    .add 849 [-10, 39] [721, 10, 69],
    .add 850 [-46, -47] [824, 92, 86, 849, 90, 68],
    .del [92],
    .add 851 [-47] [824, 850, 88, 89, 91, 66, 84],
    .add 852 [-229] [851, 848, 676],
    .add 853 [38] [852, 707, 679],
    .add 854 [-9, 34] [722, 4, 53],
    .add 855 [-37] [853, 63, 686, 854, 61, 52],
    .add 856 [-1] [855, 59],
    .add 857 [-9] [855, 60],
    .add 858 [36] [855, 853, 62],
    .add 859 [-195] [856, 857, 567],
    .add 860 [-34] [857, 856, 50],
    .add 861 [-42] [857, 856, 74],
    .add 862 [-52] [857, 856, 106],
    .add 863 [-66] [857, 856, 151],
    .add 864 [-84] [857, 856, 209],
    .add 865 [-106] [857, 856, 280],
    .add 866 [-132] [857, 856, 364],
    .add 867 [-162] [857, 856, 461],
    .add 868 [] [858, 860, 685]]

/-- The grade: the number of steps. -/
def grade8 : Nat := 215

theorem steps8_length : steps8.length = grade8 := by decide

/-- **The kernel checks the solver's certificate.** -/
theorem steps8_accepted : Lrat.check grade8 (encode (noCarry 8)) (.refutation steps8) = .ok := by
  decide +kernel

/-- **`x &&& y = 0 → x + y = x ||| y` at 8 bits**, from the certificate. -/
theorem noCarry8_holds : (noCarry 8).Holds :=
  translation.sound (r := grade8) (c := .refutation steps8) steps8_accepted

/-- The certificate with clause `687` deleted as soon as it is added. -/
def dropped : List Step := steps8.take 8 ++ [.del [687]] ++ steps8.drop 8

theorem dropped_cites : steps8[7]? = some (.add 687 [-43] [73, 78]) ∧ steps8[9]? = some (.add 688 [-44, 40] [687, 83]) := by
  decide

/-- **The tooth**: the step after the deletion cites the deleted clause and is refused, by name. -/
theorem dropped_refused : Lrat.check (grade8 + 1) (encode (noCarry 8)) (.refutation dropped) = .refused (.missingHint 687) [10] := by
  decide +kernel

end Obend.Judge.Certified
end
