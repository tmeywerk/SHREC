(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 3771041523356991 4503599627370496) r3))) (let ((.def_1 (* (/ 4169464093981201 9007199254740992) r2))) (let ((.def_2 (* (- (/ 29436895908139 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 974127084392033 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 3213458694459827 4503599627370496)))) (let ((.def_6 (* (/ 3232379248234697 9007199254740992) r3))) (let ((.def_7 (* (- (/ 3579451139196247 4503599627370496)) r2))) (let ((.def_8 (* (/ 327943779857197 1125899906842624) r1))) (let ((.def_9 (* (/ 3826062521916863 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 390070521504929 1125899906842624)))) (let ((.def_12 (or b2 .def_11 .def_5))) (let ((.def_13 (* (- (/ 3133796130928673 9007199254740992)) r3))) (let ((.def_14 (* (- (/ 1000577837858359 9007199254740992)) r2))) (let ((.def_15 (* (- (/ 5697307873030253 9007199254740992)) r1))) (let ((.def_16 (* (- (/ 5640824101432543 9007199254740992)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (- (/ 669296242833461 1125899906842624))))) (let ((.def_19 (* (- (/ 8969595495608929 9007199254740992)) r3))) (let ((.def_20 (* (- (/ 3091684738357745 2251799813685248)) r2))) (let ((.def_21 (* (- (/ 4458838262485359 9007199254740992)) r1))) (let ((.def_22 (* (/ 1194036426300689 1125899906842624) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 2120860139894545 2251799813685248))))) (let ((.def_25 (or b1 .def_24 .def_18))) (let ((.def_26 (* (- (/ 2368561667878099 4503599627370496)) r3))) (let ((.def_27 (* (/ 8809347933907919 9007199254740992) r2))) (let ((.def_28 (* (/ 2114204220851105 9007199254740992) r1))) (let ((.def_29 (* (- (/ 531946167115799 4503599627370496)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (/ 1013688545411979 4503599627370496)))) (let ((.def_32 (* (- (/ 129920196833291 2251799813685248)) r3))) (let ((.def_33 (* (- (/ 783770092870113 281474976710656)) r2))) (let ((.def_34 (* (- (/ 766378306182039 562949953421312)) r1))) (let ((.def_35 (* (/ 18247139903307 17592186044416) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (- (/ 7368845878997667 4503599627370496))))) (let ((.def_38 (or b2 .def_37 .def_31))) (let ((.def_39 (* (/ 1666928217695795 2251799813685248) r3))) (let ((.def_40 (* (- (/ 596160012240335 562949953421312)) r2))) (let ((.def_41 (* (/ 1233892103019263 2251799813685248) r1))) (let ((.def_42 (* (- (/ 2165177767214645 4503599627370496)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 672951977956485 2251799813685248)))) (let ((.def_45 (* (- (/ 866203908636413 2251799813685248)) r3))) (let ((.def_46 (* (- (/ 35721648048779 281474976710656)) r2))) (let ((.def_47 (* (/ 8685444247376025 9007199254740992) r1))) (let ((.def_48 (* (/ 473503444411057 4503599627370496) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 1466616707378483 4503599627370496)))) (let ((.def_51 (not b3))) (let ((.def_52 (or .def_51 .def_50 .def_44))) (let ((.def_53 (* (- (/ 2014178370371389 1125899906842624)) r3))) (let ((.def_54 (* (/ 1701232695971955 4503599627370496) r2))) (let ((.def_55 (* (/ 839267020586679 4503599627370496) r1))) (let ((.def_56 (* (- (/ 92867291391571 562949953421312)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 2233082194501925 9007199254740992))))) (let ((.def_59 (* (- (/ 2036631640607031 2251799813685248)) r3))) (let ((.def_60 (* (/ 110191348128711 2251799813685248) r2))) (let ((.def_61 (* (/ 111609715488523 1125899906842624) r1))) (let ((.def_62 (* (/ 6866538461779885 4503599627370496) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 1598482859825215 4503599627370496)))) (let ((.def_65 (or b3 .def_64 .def_58))) (let ((.def_66 (* (/ 5592336654432975 4503599627370496) r3))) (let ((.def_67 (* (/ 892518234246527 2251799813685248) r2))) (let ((.def_68 (* (/ 4119307098244697 2251799813685248) r1))) (let ((.def_69 (* (- (/ 1110674771520851 1125899906842624)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 3685543345994647 2251799813685248)))) (let ((.def_72 (* (- (/ 8586052095891561 2251799813685248)) r3))) (let ((.def_73 (* (/ 457085897531347 1125899906842624) r2))) (let ((.def_74 (* (/ 900768486998795 9007199254740992) r1))) (let ((.def_75 (* (- (/ 3491875427395569 4503599627370496)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (- (/ 4964836557456649 2251799813685248))))) (let ((.def_78 (or b3 .def_77 .def_71))) (let ((.def_79 (* (/ 279827513775365 562949953421312) r3))) (let ((.def_80 (* (/ 1890440572352593 4503599627370496) r2))) (let ((.def_81 (* (- (/ 718555420949317 4503599627370496)) r1))) (let ((.def_82 (* (- (/ 3038493928124209 4503599627370496)) r0))) (let ((.def_83 (+ .def_82 .def_81 .def_80 .def_79))) (let ((.def_84 (<= .def_83 (/ 179325700618089 562949953421312)))) (let ((.def_85 (* (/ 2542640075975677 1125899906842624) r3))) (let ((.def_86 (* (- (/ 93625221150963 4503599627370496)) r2))) (let ((.def_87 (* (/ 2641398296218549 4503599627370496) r1))) (let ((.def_88 (* (/ 4247855851824061 2251799813685248) r0))) (let ((.def_89 (+ .def_88 .def_87 .def_86 .def_85))) (let ((.def_90 (<= .def_89 (/ 5016369267308871 2251799813685248)))) (let ((.def_91 (not b0))) (let ((.def_92 (or .def_91 .def_90 .def_84))) (let ((.def_93 (* (/ 580774352384679 281474976710656) r3))) (let ((.def_94 (* (- (/ 4495375727750391 9007199254740992)) r2))) (let ((.def_95 (* (- (/ 2376151462802351 1125899906842624)) r1))) (let ((.def_96 (* (/ 1815107918556889 2251799813685248) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (/ 4185013597186681 9007199254740992)))) (let ((.def_99 (* (- (/ 2999574603965275 9007199254740992)) r3))) (let ((.def_100 (* (- (/ 4776430130488779 2251799813685248)) r2))) (let ((.def_101 (* (/ 4216184147624807 1125899906842624) r1))) (let ((.def_102 (* (/ 3436605684886119 2251799813685248) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (/ 436215333849031 281474976710656)))) (let ((.def_105 (or .def_51 .def_104 .def_98))) (let ((.def_106 (* (/ 2725111059821031 2251799813685248) r3))) (let ((.def_107 (* (/ 8596089342990187 4503599627370496) r2))) (let ((.def_108 (* (/ 5301151499513859 9007199254740992) r1))) (let ((.def_109 (* (/ 198788294755359 1125899906842624) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 8425496929090635 4503599627370496)))) (let ((.def_112 (* (/ 2257010907916539 9007199254740992) r3))) (let ((.def_113 (* (- (/ 817228706382747 281474976710656)) r2))) (let ((.def_114 (* (- (/ 1167846300119533 9007199254740992)) r1))) (let ((.def_115 (* (- (/ 2972844143883495 2251799813685248)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 554832335573305 281474976710656))))) (let ((.def_118 (or b0 .def_117 .def_111))) (let ((.def_119 (* (/ 2201783942811601 4503599627370496) r3))) (let ((.def_120 (* (/ 521093209957963 1125899906842624) r2))) (let ((.def_121 (* (/ 1394068812055401 9007199254740992) r1))) (let ((.def_122 (* (/ 105556397278391 2251799813685248) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (/ 2814284504356665 4503599627370496)))) (let ((.def_125 (* (- (/ 2946017711489863 1125899906842624)) r3))) (let ((.def_126 (* (/ 616977855624415 9007199254740992) r2))) (let ((.def_127 (* (- (/ 706470427748683 1125899906842624)) r1))) (let ((.def_128 (* (- (/ 104820236544819 140737488355328)) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (- (/ 2566324105007949 1125899906842624))))) (let ((.def_131 (or b0 .def_130 .def_124))) (let ((.def_132 (* (- (/ 6347364297959051 9007199254740992)) r3))) (let ((.def_133 (* (/ 1242439804585491 1125899906842624) r2))) (let ((.def_134 (* (- (/ 6102428692834717 2251799813685248)) r1))) (let ((.def_135 (* (- (/ 2531797699212257 4503599627370496)) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (- (/ 1680129332147629 2251799813685248))))) (let ((.def_138 (* (/ 3625300872921403 2251799813685248) r3))) (let ((.def_139 (* (/ 8779950168398695 9007199254740992) r2))) (let ((.def_140 (* (- (/ 7555301445252649 9007199254740992)) r1))) (let ((.def_141 (* (/ 2620423396960549 2251799813685248) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (/ 3169182497983599 2251799813685248)))) (let ((.def_144 (or b0 .def_143 .def_137))) (let ((.def_145 (* (- (/ 3497403641470641 2251799813685248)) r3))) (let ((.def_146 (* (/ 184965208796855 1125899906842624) r2))) (let ((.def_147 (* (- (/ 5694562120856485 9007199254740992)) r1))) (let ((.def_148 (* (- (/ 1599191608149667 4503599627370496)) r0))) (let ((.def_149 (+ .def_148 .def_147 .def_146 .def_145))) (let ((.def_150 (<= .def_149 (- (/ 2355971342109293 4503599627370496))))) (let ((.def_151 (* (- (/ 3064637899118911 2251799813685248)) r3))) (let ((.def_152 (* (/ 621402578205055 562949953421312) r2))) (let ((.def_153 (* (/ 2358813440831085 9007199254740992) r1))) (let ((.def_154 (* (/ 7476896939216339 9007199254740992) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (/ 1607115582381295 4503599627370496)))) (let ((.def_157 (or b3 .def_156 .def_150))) (let ((.def_158 (* (- (/ 2019826107382059 2251799813685248)) r3))) (let ((.def_159 (* (- (/ 4202625302772697 9007199254740992)) r2))) (let ((.def_160 (* (- (/ 1932241488364947 2251799813685248)) r1))) (let ((.def_161 (* (/ 3094842175263737 4503599627370496) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (- (/ 1553228215701591 4503599627370496))))) (let ((.def_164 (* (- (/ 2134816614740187 4503599627370496)) r3))) (let ((.def_165 (* (/ 4288285332508273 4503599627370496) r2))) (let ((.def_166 (* (- (/ 739877953217951 2251799813685248)) r1))) (let ((.def_167 (* (- (/ 4299185701604915 4503599627370496)) r0))) (let ((.def_168 (+ .def_167 .def_166 .def_165 .def_164))) (let ((.def_169 (<= .def_168 (- (/ 2182083918072455 4503599627370496))))) (let ((.def_170 (or b0 .def_169 .def_163))) (let ((.def_171 (* (/ 4016975782311631 9007199254740992) r3))) (let ((.def_172 (* (/ 670616388395729 562949953421312) r2))) (let ((.def_173 (* (- (/ 5197969786170809 4503599627370496)) r1))) (let ((.def_174 (* (- (/ 4453555992113809 2251799813685248)) r0))) (let ((.def_175 (+ .def_174 .def_173 .def_172 .def_171))) (let ((.def_176 (<= .def_175 (/ 2029504661032243 9007199254740992)))) (let ((.def_177 (* (/ 3249728291936571 2251799813685248) r3))) (let ((.def_178 (* (- (/ 170183910575615 4503599627370496)) r2))) (let ((.def_179 (* (- (/ 5500045073726235 9007199254740992)) r1))) (let ((.def_180 (* (- (/ 7932228099351313 9007199254740992)) r0))) (let ((.def_181 (+ .def_180 .def_179 .def_178 .def_177))) (let ((.def_182 (<= .def_181 (- (/ 77185705599185 1125899906842624))))) (let ((.def_183 (or b1 .def_182 .def_176))) (let ((.def_184 (and .def_183 .def_170 .def_157 .def_144 .def_131 .def_118 .def_105 .def_92 .def_78 .def_65 .def_52 .def_38 .def_25 .def_12))) .def_184))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)