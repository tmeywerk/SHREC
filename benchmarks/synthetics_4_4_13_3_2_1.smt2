(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun b0 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (- (/ 2615404585231 281474976710656)) r3))) (let ((.def_1 (* (- (/ 779641282699345 562949953421312)) r2))) (let ((.def_2 (* (/ 252732927493735 2251799813685248) r1))) (let ((.def_3 (* (- (/ 718399741483731 1125899906842624)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1870854574474969 2251799813685248))))) (let ((.def_6 (* (/ 3212830890275025 2251799813685248) r3))) (let ((.def_7 (* (- (/ 1700640263035225 9007199254740992)) r2))) (let ((.def_8 (* (- (/ 3255353471793185 9007199254740992)) r1))) (let ((.def_9 (* (/ 6533830291203605 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 2575589474111701 2251799813685248)))) (let ((.def_12 (or b3 .def_11 .def_5))) (let ((.def_13 (* (- (/ 4097019720947137 2251799813685248)) r3))) (let ((.def_14 (* (/ 5315508943020539 2251799813685248) r2))) (let ((.def_15 (* (- (/ 7185167925874039 9007199254740992)) r1))) (let ((.def_16 (* (- (/ 5406043122668057 9007199254740992)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 1815104910413115 4503599627370496)))) (let ((.def_19 (* (- (/ 2338042315720659 2251799813685248)) r3))) (let ((.def_20 (* (- (/ 505651014946199 1125899906842624)) r2))) (let ((.def_21 (* (- (/ 1680185179851687 1125899906842624)) r1))) (let ((.def_22 (* (/ 2743548398357579 4503599627370496) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 372117143667893 281474976710656))))) (let ((.def_25 (or b3 .def_24 .def_18))) (let ((.def_26 (* (/ 118363643554445 562949953421312) r3))) (let ((.def_27 (* (- (/ 1301562094351681 2251799813685248)) r2))) (let ((.def_28 (* (- (/ 2049872243788381 4503599627370496)) r1))) (let ((.def_29 (* (/ 121565962388153 562949953421312) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (- (/ 263641980556689 9007199254740992))))) (let ((.def_32 (* (- (/ 405076430033961 2251799813685248)) r3))) (let ((.def_33 (* (- (/ 4446494026010335 4503599627370496)) r2))) (let ((.def_34 (* (- (/ 5871705937169709 4503599627370496)) r1))) (let ((.def_35 (* (/ 625049126502929 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (- (/ 2646282804429447 2251799813685248))))) (let ((.def_38 (or b3 .def_37 .def_31))) (let ((.def_39 (* (/ 2170290553584631 4503599627370496) r3))) (let ((.def_40 (* (- (/ 4453640036388277 4503599627370496)) r2))) (let ((.def_41 (* (- (/ 286354820962119 2251799813685248)) r1))) (let ((.def_42 (* (/ 669520759014211 562949953421312) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 4038672229939243 4503599627370496)))) (let ((.def_45 (* (/ 4057155657051487 4503599627370496) r3))) (let ((.def_46 (* (- (/ 6084800949385411 9007199254740992)) r2))) (let ((.def_47 (* (- (/ 1695274839218375 4503599627370496)) r1))) (let ((.def_48 (* (/ 5957274847233123 4503599627370496) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 48183833286315 70368744177664)))) (let ((.def_51 (not b0))) (let ((.def_52 (or .def_51 .def_50 .def_44))) (let ((.def_53 (* (- (/ 1380719361119703 4503599627370496)) r3))) (let ((.def_54 (* (/ 2918474458188801 2251799813685248) r2))) (let ((.def_55 (* (- (/ 3282679888622733 2251799813685248)) r1))) (let ((.def_56 (* (- (/ 2479456710819839 9007199254740992)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 2753351551977131 9007199254740992)))) (let ((.def_59 (* (/ 2150343967197737 9007199254740992) r3))) (let ((.def_60 (* (/ 3848523885873195 4503599627370496) r2))) (let ((.def_61 (* (- (/ 7309125641503645 9007199254740992)) r1))) (let ((.def_62 (* (- (/ 4334160466895217 9007199254740992)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 152496690260271 1125899906842624))))) (let ((.def_65 (not b1))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (* (- (/ 50431998733381 2251799813685248)) r3))) (let ((.def_68 (* (/ 8829971721627749 4503599627370496) r2))) (let ((.def_69 (* (- (/ 11225298550685 1125899906842624)) r1))) (let ((.def_70 (* (- (/ 6161403467697383 9007199254740992)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 4314656819246819 4503599627370496)))) (let ((.def_73 (* (/ 2475911000646737 2251799813685248) r3))) (let ((.def_74 (* (- (/ 239534929474337 281474976710656)) r2))) (let ((.def_75 (* (- (/ 2560643906116543 4503599627370496)) r1))) (let ((.def_76 (* (/ 809946056133885 9007199254740992) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 317697768760693 2251799813685248))))) (let ((.def_79 (or b2 .def_78 .def_72))) (let ((.def_80 (* (- (/ 167674596507735 281474976710656)) r3))) (let ((.def_81 (* (- (/ 28649436380721 562949953421312)) r2))) (let ((.def_82 (* (- (/ 3921329515170609 4503599627370496)) r1))) (let ((.def_83 (* (- (/ 442037966849181 2251799813685248)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (- (/ 1572415084967985 2251799813685248))))) (let ((.def_86 (* (/ 2705107370543649 2251799813685248) r3))) (let ((.def_87 (* (/ 680656465111057 562949953421312) r2))) (let ((.def_88 (* (/ 3640006885042275 2251799813685248) r1))) (let ((.def_89 (* (- (/ 4915666364966967 2251799813685248)) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 5958089221154411 9007199254740992)))) (let ((.def_92 (not b2))) (let ((.def_93 (or .def_92 .def_91 .def_85))) (let ((.def_94 (* (- (/ 1507313079573263 9007199254740992)) r3))) (let ((.def_95 (* (- (/ 4047143553813777 4503599627370496)) r2))) (let ((.def_96 (* (/ 222622732879697 562949953421312) r1))) (let ((.def_97 (* (- (/ 9603440234333 2251799813685248)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 1929954857600617 9007199254740992))))) (let ((.def_100 (* (/ 1954833060114835 1125899906842624) r3))) (let ((.def_101 (* (/ 2888352318398003 2251799813685248) r2))) (let ((.def_102 (* (- (/ 7601036346849991 2251799813685248)) r1))) (let ((.def_103 (* (- (/ 2075447645516051 4503599627370496)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 2247488604664743 4503599627370496))))) (let ((.def_106 (not b3))) (let ((.def_107 (or .def_106 .def_105 .def_99))) (let ((.def_108 (* (- (/ 1217717424128109 4503599627370496)) r3))) (let ((.def_109 (* (- (/ 341460990166283 4503599627370496)) r2))) (let ((.def_110 (* (- (/ 87415896775791 4503599627370496)) r1))) (let ((.def_111 (* (- (/ 2507018408824815 4503599627370496)) r0))) (let ((.def_112 (+ .def_111 .def_110 .def_109 .def_108))) (let ((.def_113 (<= .def_112 (- (/ 726716387945043 2251799813685248))))) (let ((.def_114 (* (- (/ 1541626148875477 2251799813685248)) r3))) (let ((.def_115 (* (- (/ 183098369080379 140737488355328)) r2))) (let ((.def_116 (* (- (/ 7407335782200919 4503599627370496)) r1))) (let ((.def_117 (* (/ 7144200676118243 4503599627370496) r0))) (let ((.def_118 (+ .def_117 .def_116 .def_115 .def_114))) (let ((.def_119 (<= .def_118 (- (/ 1268279225094657 1125899906842624))))) (let ((.def_120 (or b1 .def_119 .def_113))) (let ((.def_121 (* (- (/ 412915785999851 2251799813685248)) r3))) (let ((.def_122 (* (/ 1837084669561839 1125899906842624) r2))) (let ((.def_123 (* (/ 2207094037453033 2251799813685248) r1))) (let ((.def_124 (* (- (/ 2577292096788015 2251799813685248)) r0))) (let ((.def_125 (+ .def_124 .def_123 .def_122 .def_121))) (let ((.def_126 (<= .def_125 (/ 3396914738776881 2251799813685248)))) (let ((.def_127 (* (- (/ 3426011105452213 4503599627370496)) r3))) (let ((.def_128 (* (/ 348557217965811 562949953421312) r2))) (let ((.def_129 (* (/ 11797191464717 17592186044416) r1))) (let ((.def_130 (* (- (/ 8232934150127647 4503599627370496)) r0))) (let ((.def_131 (+ .def_130 .def_129 .def_128 .def_127))) (let ((.def_132 (<= .def_131 (- (/ 7573601536465423 9007199254740992))))) (let ((.def_133 (or b1 .def_132 .def_126))) (let ((.def_134 (* (/ 3610214369804305 4503599627370496) r3))) (let ((.def_135 (* (/ 2636661698979727 4503599627370496) r2))) (let ((.def_136 (* (/ 1669064313204679 4503599627370496) r1))) (let ((.def_137 (* (- (/ 200817616298929 281474976710656)) r0))) (let ((.def_138 (+ .def_137 .def_136 .def_135 .def_134))) (let ((.def_139 (<= .def_138 (/ 4868986018486425 4503599627370496)))) (let ((.def_140 (* (/ 4262411288008047 4503599627370496) r3))) (let ((.def_141 (* (- (/ 1635775801059177 9007199254740992)) r2))) (let ((.def_142 (* (/ 7247427423271421 9007199254740992) r1))) (let ((.def_143 (* (/ 946575042269915 4503599627370496) r0))) (let ((.def_144 (+ .def_143 .def_142 .def_141 .def_140))) (let ((.def_145 (<= .def_144 (/ 7924499954027985 9007199254740992)))) (let ((.def_146 (or b3 .def_145 .def_139))) (let ((.def_147 (* (- (/ 2324709963486327 2251799813685248)) r3))) (let ((.def_148 (* (- (/ 135365429231261 562949953421312)) r2))) (let ((.def_149 (* (/ 5314287458655823 4503599627370496) r1))) (let ((.def_150 (* (- (/ 4712324979451515 4503599627370496)) r0))) (let ((.def_151 (+ .def_150 .def_149 .def_148 .def_147))) (let ((.def_152 (<= .def_151 (/ 615511672247833 9007199254740992)))) (let ((.def_153 (* (- (/ 4469169062896187 2251799813685248)) r3))) (let ((.def_154 (* (- (/ 1995700146923489 562949953421312)) r2))) (let ((.def_155 (* (/ 294294226663617 140737488355328) r1))) (let ((.def_156 (* (/ 4627035602718035 4503599627370496) r0))) (let ((.def_157 (+ .def_156 .def_155 .def_154 .def_153))) (let ((.def_158 (<= .def_157 (- (/ 3222322275759197 2251799813685248))))) (let ((.def_159 (or .def_65 .def_158 .def_152))) (let ((.def_160 (* (/ 1585490945698001 4503599627370496) r3))) (let ((.def_161 (* (- (/ 2336502063192775 4503599627370496)) r2))) (let ((.def_162 (* (/ 1101505589537111 4503599627370496) r1))) (let ((.def_163 (* (- (/ 490239407133155 1125899906842624)) r0))) (let ((.def_164 (+ .def_163 .def_162 .def_161 .def_160))) (let ((.def_165 (<= .def_164 (- (/ 35224981765629 562949953421312))))) (let ((.def_166 (* (- (/ 1090915151854633 562949953421312)) r3))) (let ((.def_167 (* (/ 3811434994619513 1125899906842624) r2))) (let ((.def_168 (* (- (/ 4396140894317833 4503599627370496)) r1))) (let ((.def_169 (* (- (/ 4102461999684875 2251799813685248)) r0))) (let ((.def_170 (+ .def_169 .def_168 .def_167 .def_166))) (let ((.def_171 (<= .def_170 (- (/ 7187774779736295 9007199254740992))))) (let ((.def_172 (or .def_65 .def_171 .def_165))) (let ((.def_173 (and .def_172 .def_159 .def_146 .def_133 .def_120 .def_107 .def_93 .def_79 .def_66 .def_52 .def_38 .def_25 .def_12))) .def_173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
