(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 33377719343499 140737488355328) r3))) (let ((.def_1 (* (- (/ 901778042089549 9007199254740992)) r2))) (let ((.def_2 (* (/ 2842801071707065 2251799813685248) r1))) (let ((.def_3 (* (- (/ 1550551158501139 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1728595829098821 2251799813685248)))) (let ((.def_6 (or b0 b2 .def_5))) (let ((.def_7 (* (/ 1391142572687515 4503599627370496) r3))) (let ((.def_8 (* (- (/ 3422297247982909 9007199254740992)) r2))) (let ((.def_9 (* (/ 6820781043883705 9007199254740992) r1))) (let ((.def_10 (* (- (/ 688398765557873 4503599627370496)) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (/ 4231448616093185 9007199254740992)))) (let ((.def_13 (not b1))) (let ((.def_14 (or .def_13 b0 .def_12))) (let ((.def_15 (* (- (/ 1715808470023731 2251799813685248)) r3))) (let ((.def_16 (* (- (/ 91803116951671 2251799813685248)) r2))) (let ((.def_17 (* (/ 2787225783926877 2251799813685248) r1))) (let ((.def_18 (* (- (/ 419172489669783 2251799813685248)) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 2718605174290157 4503599627370496)))) (let ((.def_21 (not b0))) (let ((.def_22 (not b2))) (let ((.def_23 (or .def_22 .def_21 .def_20))) (let ((.def_24 (* (- (/ 3246291213083083 2251799813685248)) r3))) (let ((.def_25 (* (- (/ 385568236914167 2251799813685248)) r2))) (let ((.def_26 (* (- (/ 3614623895733525 4503599627370496)) r1))) (let ((.def_27 (* (/ 1372959152264863 2251799813685248) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 3880183890997029 9007199254740992))))) (let ((.def_30 (or .def_21 b2 .def_29))) (let ((.def_31 (* (/ 1680524066577641 2251799813685248) r3))) (let ((.def_32 (* (/ 4873098069710469 4503599627370496) r2))) (let ((.def_33 (* (/ 336020688694529 562949953421312) r1))) (let ((.def_34 (* (- (/ 3870948398750975 4503599627370496)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 6345657740800407 4503599627370496)))) (let ((.def_37 (or b2 b0 .def_36))) (let ((.def_38 (* (- (/ 3308871604195111 9007199254740992)) r3))) (let ((.def_39 (* (- (/ 1311896597766515 4503599627370496)) r2))) (let ((.def_40 (* (/ 826202728274743 9007199254740992) r1))) (let ((.def_41 (* (- (/ 1635412977369513 1125899906842624)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 5577865016382667 9007199254740992))))) (let ((.def_44 (not b3))) (let ((.def_45 (or .def_22 .def_44 .def_43))) (let ((.def_46 (* (- (/ 844157791792095 2251799813685248)) r3))) (let ((.def_47 (* (- (/ 7748624251412205 9007199254740992)) r2))) (let ((.def_48 (* (- (/ 3309756284637681 4503599627370496)) r1))) (let ((.def_49 (* (- (/ 6230469185097201 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 2379186001978801 2251799813685248))))) (let ((.def_52 (or b3 .def_13 .def_51))) (let ((.def_53 (* (- (/ 215493652487743 562949953421312)) r3))) (let ((.def_54 (* (- (/ 193956495353119 2251799813685248)) r2))) (let ((.def_55 (* (/ 5093483683181239 4503599627370496) r1))) (let ((.def_56 (* (- (/ 27714242750441 70368744177664)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 4838732380673139 9007199254740992)))) (let ((.def_59 (or .def_44 .def_21 .def_58))) (let ((.def_60 (* (/ 3510780220259039 9007199254740992) r3))) (let ((.def_61 (* (- (/ 4789860336274621 9007199254740992)) r2))) (let ((.def_62 (* (/ 985567020351647 2251799813685248) r1))) (let ((.def_63 (* (/ 1134050714082537 562949953421312) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 2280562531604883 1125899906842624)))) (let ((.def_66 (or b3 .def_21 .def_65))) (let ((.def_67 (* (/ 4873099836757735 4503599627370496) r3))) (let ((.def_68 (* (- (/ 25495166158481 17592186044416)) r2))) (let ((.def_69 (* (/ 2167927123098523 2251799813685248) r1))) (let ((.def_70 (* (/ 1099877079343775 4503599627370496) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 4948095915977427 4503599627370496)))) (let ((.def_73 (or b3 .def_13 .def_72))) (let ((.def_74 (* (/ 3531464521349477 9007199254740992) r3))) (let ((.def_75 (* (- (/ 2354363264901367 2251799813685248)) r2))) (let ((.def_76 (* (/ 4048665157262147 9007199254740992) r1))) (let ((.def_77 (* (/ 356048447291461 562949953421312) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 3240787858188961 4503599627370496)))) (let ((.def_80 (or b0 .def_13 .def_79))) (let ((.def_81 (* (- (/ 622927891648443 9007199254740992)) r3))) (let ((.def_82 (* (- (/ 70166833395491 2251799813685248)) r2))) (let ((.def_83 (* (- (/ 1339987480220641 1125899906842624)) r1))) (let ((.def_84 (* (- (/ 755553665130229 1125899906842624)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 2954979287261885 9007199254740992))))) (let ((.def_87 (or .def_44 b1 .def_86))) (let ((.def_88 (* (- (/ 2843927406794011 2251799813685248)) r3))) (let ((.def_89 (* (- (/ 1296540782917315 1125899906842624)) r2))) (let ((.def_90 (* (/ 2407033985959285 2251799813685248) r1))) (let ((.def_91 (* (- (/ 5285859080094519 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 1583501497680289 2251799813685248))))) (let ((.def_94 (or b2 b3 .def_93))) (let ((.def_95 (* (/ 2243367948669721 4503599627370496) r3))) (let ((.def_96 (* (- (/ 2824590353518807 4503599627370496)) r2))) (let ((.def_97 (* (- (/ 15733412117863 17592186044416)) r1))) (let ((.def_98 (* (- (/ 1921484278626609 4503599627370496)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 392489666279257 1125899906842624))))) (let ((.def_101 (or .def_22 b0 .def_100))) (let ((.def_102 (* (- (/ 468106444943175 4503599627370496)) r3))) (let ((.def_103 (* (- (/ 6510029531212379 9007199254740992)) r2))) (let ((.def_104 (* (- (/ 382582110263703 1125899906842624)) r1))) (let ((.def_105 (* (- (/ 1360194038103025 1125899906842624)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 7382778046058637 9007199254740992))))) (let ((.def_108 (or b0 .def_22 .def_107))) (let ((.def_109 (* (- (/ 678194902118145 281474976710656)) r3))) (let ((.def_110 (* (- (/ 1045498523627369 1125899906842624)) r2))) (let ((.def_111 (* (/ 1097920529939909 4503599627370496) r1))) (let ((.def_112 (* (- (/ 3483155336288799 9007199254740992)) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (- (/ 3460959388400547 4503599627370496))))) (let ((.def_115 (or .def_22 .def_13 .def_114))) (let ((.def_116 (* (/ 3648208071797853 9007199254740992) r3))) (let ((.def_117 (* (- (/ 30960920186079 1125899906842624)) r2))) (let ((.def_118 (* (- (/ 3009122691654713 4503599627370496)) r1))) (let ((.def_119 (* (- (/ 1433890893418591 1125899906842624)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 1066317469796219 9007199254740992))))) (let ((.def_122 (or .def_22 .def_13 .def_121))) (let ((.def_123 (* (- (/ 8119854519793435 9007199254740992)) r3))) (let ((.def_124 (* (- (/ 2352115776889453 4503599627370496)) r2))) (let ((.def_125 (* (- (/ 1634075262923767 4503599627370496)) r1))) (let ((.def_126 (* (- (/ 982679685317861 9007199254740992)) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (- (/ 2457595209353575 4503599627370496))))) (let ((.def_129 (or .def_13 b2 .def_128))) (let ((.def_130 (* (- (/ 4486346102978655 9007199254740992)) r3))) (let ((.def_131 (* (- (/ 1349110339693665 4503599627370496)) r2))) (let ((.def_132 (* (/ 2435675890548561 4503599627370496) r1))) (let ((.def_133 (* (- (/ 1036400427052757 2251799813685248)) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (- (/ 422183556120399 9007199254740992))))) (let ((.def_136 (or b3 b1 .def_135))) (let ((.def_137 (* (- (/ 71970970432433 281474976710656)) r3))) (let ((.def_138 (* (- (/ 1063967410733151 1125899906842624)) r2))) (let ((.def_139 (* (/ 2135107825217987 4503599627370496) r1))) (let ((.def_140 (* (/ 5616905241529865 4503599627370496) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (/ 7819402723930821 9007199254740992)))) (let ((.def_143 (or b1 .def_44 .def_142))) (let ((.def_144 (* (- (/ 1878463722126705 9007199254740992)) r3))) (let ((.def_145 (* (- (/ 398776197746279 4503599627370496)) r2))) (let ((.def_146 (* (- (/ 2265986483723581 4503599627370496)) r1))) (let ((.def_147 (* (/ 2657801367151525 4503599627370496) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (/ 544576112219971 2251799813685248)))) (let ((.def_150 (or b3 .def_22 .def_149))) (let ((.def_151 (* (/ 1241201162116783 1125899906842624) r3))) (let ((.def_152 (* (- (/ 1517726819942833 9007199254740992)) r2))) (let ((.def_153 (* (- (/ 228028497580161 4503599627370496)) r1))) (let ((.def_154 (* (- (/ 5756149703886221 4503599627370496)) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (/ 1235416835631831 2251799813685248)))) (let ((.def_157 (or .def_44 b0 .def_156))) (let ((.def_158 (* (- (/ 113615535220789 281474976710656)) r3))) (let ((.def_159 (* (- (/ 3357860236654531 9007199254740992)) r2))) (let ((.def_160 (* (/ 2780449233244367 2251799813685248) r1))) (let ((.def_161 (* (- (/ 6966102850008677 4503599627370496)) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (/ 1927611729056199 9007199254740992)))) (let ((.def_164 (or b2 .def_44 .def_163))) (let ((.def_165 (and .def_164 .def_157 .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_37 .def_30 .def_23 .def_14 .def_6))) .def_165)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)