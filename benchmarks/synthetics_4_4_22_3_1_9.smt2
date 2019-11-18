(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (/ 8837604290728751 9007199254740992) r3))) (let ((.def_1 (* (/ 2488119297151539 9007199254740992) r2))) (let ((.def_2 (* (- (/ 6190597739765891 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 3537372720312297 1125899906842624)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 4097180411567461 9007199254740992))))) (let ((.def_6 (or b3 b1 .def_5))) (let ((.def_7 (* (/ 7533482011984719 4503599627370496) r3))) (let ((.def_8 (* (- (/ 3360464108609541 4503599627370496)) r2))) (let ((.def_9 (* (- (/ 3487374239950849 4503599627370496)) r1))) (let ((.def_10 (* (- (/ 1995969153357391 4503599627370496)) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (/ 2964692476533077 9007199254740992)))) (let ((.def_13 (not b1))) (let ((.def_14 (not b3))) (let ((.def_15 (or .def_14 .def_13 .def_12))) (let ((.def_16 (* (- (/ 1408494160409555 9007199254740992)) r3))) (let ((.def_17 (* (- (/ 858113954059565 281474976710656)) r2))) (let ((.def_18 (* (/ 4354858546174295 4503599627370496) r1))) (let ((.def_19 (* (- (/ 2028254996153259 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 1926768718566217 2251799813685248))))) (let ((.def_22 (or b2 b0 .def_21))) (let ((.def_23 (* (/ 3327535649396857 2251799813685248) r3))) (let ((.def_24 (* (- (/ 840220431369161 9007199254740992)) r2))) (let ((.def_25 (* (- (/ 1396884350106491 2251799813685248)) r1))) (let ((.def_26 (* (- (/ 5864230829918783 9007199254740992)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (/ 2690625727771155 4503599627370496)))) (let ((.def_29 (or b0 .def_14 .def_28))) (let ((.def_30 (* (- (/ 1349774192283479 562949953421312)) r3))) (let ((.def_31 (* (- (/ 800368421142009 1125899906842624)) r2))) (let ((.def_32 (* (/ 672949611985771 4503599627370496) r1))) (let ((.def_33 (* (/ 28346074859445 140737488355328) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (- (/ 4595242034587371 9007199254740992))))) (let ((.def_36 (not b0))) (let ((.def_37 (or .def_36 b3 .def_35))) (let ((.def_38 (* (- (/ 309359321252563 1125899906842624)) r3))) (let ((.def_39 (* (- (/ 6104282099854563 4503599627370496)) r2))) (let ((.def_40 (* (/ 2307842037689979 4503599627370496) r1))) (let ((.def_41 (* (/ 4477492733059427 4503599627370496) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 190773389786235 562949953421312)))) (let ((.def_44 (or b2 .def_13 .def_43))) (let ((.def_45 (* (/ 653009017493323 1125899906842624) r3))) (let ((.def_46 (* (/ 2733777262590947 4503599627370496) r2))) (let ((.def_47 (* (/ 368818836261427 4503599627370496) r1))) (let ((.def_48 (* (- (/ 382902018654681 2251799813685248)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 3869921276284007 4503599627370496)))) (let ((.def_51 (not b2))) (let ((.def_52 (or .def_51 b3 .def_50))) (let ((.def_53 (* (/ 24736790981043 562949953421312) r3))) (let ((.def_54 (* (/ 3798728455602181 9007199254740992) r2))) (let ((.def_55 (* (/ 305759873037593 1125899906842624) r1))) (let ((.def_56 (* (/ 1213460970104453 2251799813685248) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 2012651006025653 2251799813685248)))) (let ((.def_59 (or .def_51 .def_36 .def_58))) (let ((.def_60 (* (- (/ 2984246771078847 9007199254740992)) r3))) (let ((.def_61 (* (/ 68575190046045 4503599627370496) r2))) (let ((.def_62 (* (- (/ 2688609479844531 1125899906842624)) r1))) (let ((.def_63 (* (- (/ 2244303934870841 9007199254740992)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 2971796009578173 4503599627370496))))) (let ((.def_66 (or b1 b2 .def_65))) (let ((.def_67 (* (- (/ 225971495889879 1125899906842624)) r3))) (let ((.def_68 (* (- (/ 4793100646111999 2251799813685248)) r2))) (let ((.def_69 (* (/ 3204793457014661 2251799813685248) r1))) (let ((.def_70 (* (- (/ 2180185846376621 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 54007937072015 9007199254740992))))) (let ((.def_73 (or b0 b2 .def_72))) (let ((.def_74 (* (- (/ 2609612779451453 4503599627370496)) r3))) (let ((.def_75 (* (- (/ 1626999706156453 4503599627370496)) r2))) (let ((.def_76 (* (- (/ 3082324392864373 2251799813685248)) r1))) (let ((.def_77 (* (/ 1112429635301657 1125899906842624) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 160379686676523 1125899906842624))))) (let ((.def_80 (or b0 b2 .def_79))) (let ((.def_81 (* (/ 4107448681369093 4503599627370496) r3))) (let ((.def_82 (* (- (/ 532065236978511 562949953421312)) r2))) (let ((.def_83 (* (- (/ 4086446219921359 2251799813685248)) r1))) (let ((.def_84 (* (- (/ 3527582231830265 4503599627370496)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 413658157851629 1125899906842624))))) (let ((.def_87 (or .def_14 b2 .def_86))) (let ((.def_88 (* (/ 2432253134693199 4503599627370496) r3))) (let ((.def_89 (* (/ 325137622340321 4503599627370496) r2))) (let ((.def_90 (* (- (/ 655002788531123 1125899906842624)) r1))) (let ((.def_91 (* (/ 3402583100613839 2251799813685248) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (/ 1646676221939983 1125899906842624)))) (let ((.def_94 (or b2 b1 .def_93))) (let ((.def_95 (* (- (/ 489799197020013 1125899906842624)) r3))) (let ((.def_96 (* (/ 28916214871641 9007199254740992) r2))) (let ((.def_97 (* (- (/ 757011856651405 2251799813685248)) r1))) (let ((.def_98 (* (- (/ 3573795856590477 9007199254740992)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 1763445019679077 4503599627370496))))) (let ((.def_101 (or .def_51 b1 .def_100))) (let ((.def_102 (* (- (/ 635888839523101 1125899906842624)) r3))) (let ((.def_103 (* (/ 2771298494484091 4503599627370496) r2))) (let ((.def_104 (* (/ 1567397417419937 2251799813685248) r1))) (let ((.def_105 (* (- (/ 709464465919451 4503599627370496)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (/ 801880957474675 1125899906842624)))) (let ((.def_108 (or .def_14 .def_51 .def_107))) (let ((.def_109 (* (/ 1001850580371187 4503599627370496) r3))) (let ((.def_110 (* (/ 6273323809656669 9007199254740992) r2))) (let ((.def_111 (* (- (/ 1454057712815121 1125899906842624)) r1))) (let ((.def_112 (* (/ 589150476264143 4503599627370496) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 1582988872243039 4503599627370496)))) (let ((.def_115 (or b1 .def_51 .def_114))) (let ((.def_116 (* (/ 3610956164408827 9007199254740992) r3))) (let ((.def_117 (* (- (/ 126515556863095 2251799813685248)) r2))) (let ((.def_118 (* (- (/ 4020204151394493 2251799813685248)) r1))) (let ((.def_119 (* (- (/ 4000563833304823 9007199254740992)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 1261358148645061 4503599627370496))))) (let ((.def_122 (or .def_51 b3 .def_121))) (let ((.def_123 (* (/ 6233203479767767 9007199254740992) r3))) (let ((.def_124 (* (/ 1020898580022803 1125899906842624) r2))) (let ((.def_125 (* (/ 1007801821259839 4503599627370496) r1))) (let ((.def_126 (* (- (/ 6282184310184747 9007199254740992)) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (/ 2408222057942817 2251799813685248)))) (let ((.def_129 (or .def_14 .def_36 .def_128))) (let ((.def_130 (* (- (/ 5009431462968217 2251799813685248)) r3))) (let ((.def_131 (* (- (/ 6005529117867721 9007199254740992)) r2))) (let ((.def_132 (* (/ 2566180580028999 2251799813685248) r1))) (let ((.def_133 (* (- (/ 1936343093909825 2251799813685248)) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (- (/ 44792149675849 1125899906842624))))) (let ((.def_136 (or .def_51 .def_14 .def_135))) (let ((.def_137 (* (- (/ 6903379486329077 9007199254740992)) r3))) (let ((.def_138 (* (- (/ 8067857597012601 9007199254740992)) r2))) (let ((.def_139 (* (/ 2461933758822951 9007199254740992) r1))) (let ((.def_140 (* (/ 6366622928445877 4503599627370496) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (/ 1616700229274593 2251799813685248)))) (let ((.def_143 (or .def_14 b2 .def_142))) (let ((.def_144 (* (- (/ 1195300194329043 9007199254740992)) r3))) (let ((.def_145 (* (- (/ 1390753649508425 1125899906842624)) r2))) (let ((.def_146 (* (/ 2133655026303401 2251799813685248) r1))) (let ((.def_147 (* (- (/ 2622516490583175 4503599627370496)) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (/ 1283066734132341 9007199254740992)))) (let ((.def_150 (or b0 b3 .def_149))) (let ((.def_151 (* (/ 4437246634738941 4503599627370496) r3))) (let ((.def_152 (* (- (/ 3436604725353007 2251799813685248)) r2))) (let ((.def_153 (* (- (/ 115944253187727 562949953421312)) r1))) (let ((.def_154 (* (- (/ 8207264301247307 9007199254740992)) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (/ 25426801144673 1125899906842624)))) (let ((.def_157 (or .def_36 b2 .def_156))) (let ((.def_158 (and .def_157 .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_37 .def_29 .def_22 .def_15 .def_6))) .def_158))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)