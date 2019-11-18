(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (- (/ 2029230496536655 4503599627370496)) r3))) (let ((.def_1 (* (/ 209715960805055 1125899906842624) r2))) (let ((.def_2 (* (/ 6736600844034789 9007199254740992) r1))) (let ((.def_3 (* (/ 2327142335712439 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 3073343190728267 4503599627370496)))) (let ((.def_6 (not b0))) (let ((.def_7 (or b2 .def_6 .def_5))) (let ((.def_8 (* (- (/ 1832169494225615 1125899906842624)) r3))) (let ((.def_9 (* (/ 3488292394561211 4503599627370496) r2))) (let ((.def_10 (* (/ 69828061966033 2251799813685248) r1))) (let ((.def_11 (* (/ 4349138812619735 4503599627370496) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 7422203287575983 9007199254740992)))) (let ((.def_14 (or b1 b3 .def_13))) (let ((.def_15 (* (- (/ 7168229425656085 9007199254740992)) r3))) (let ((.def_16 (* (- (/ 2020105914034345 2251799813685248)) r2))) (let ((.def_17 (* (/ 374453824082895 2251799813685248) r1))) (let ((.def_18 (* (/ 8838512892324343 9007199254740992) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 133611550915357 4503599627370496)))) (let ((.def_21 (or b2 .def_6 .def_20))) (let ((.def_22 (* (- (/ 788246766981871 1125899906842624)) r3))) (let ((.def_23 (* (- (/ 3693781908833149 4503599627370496)) r2))) (let ((.def_24 (* (- (/ 2176727356813131 4503599627370496)) r1))) (let ((.def_25 (* (- (/ 279461060448899 281474976710656)) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (- (/ 282332934551703 281474976710656))))) (let ((.def_28 (or b2 b3 .def_27))) (let ((.def_29 (* (/ 684324859616139 562949953421312) r3))) (let ((.def_30 (* (/ 1096339438538423 4503599627370496) r2))) (let ((.def_31 (* (- (/ 162331570287341 140737488355328)) r1))) (let ((.def_32 (* (/ 1228934148469789 9007199254740992) r0))) (let ((.def_33 (+ .def_32 .def_31 .def_30 .def_29))) (let ((.def_34 (<= .def_33 (/ 5637235107614545 9007199254740992)))) (let ((.def_35 (not b1))) (let ((.def_36 (or .def_6 .def_35 .def_34))) (let ((.def_37 (* (/ 8376649822673503 9007199254740992) r3))) (let ((.def_38 (* (/ 21816985126539 1125899906842624) r2))) (let ((.def_39 (* (- (/ 680095291600621 562949953421312)) r1))) (let ((.def_40 (* (- (/ 1171789167749873 9007199254740992)) r0))) (let ((.def_41 (+ .def_40 .def_39 .def_38 .def_37))) (let ((.def_42 (<= .def_41 (/ 1409666604992415 4503599627370496)))) (let ((.def_43 (not b3))) (let ((.def_44 (or .def_43 b1 .def_42))) (let ((.def_45 (* (/ 2587231641900827 4503599627370496) r3))) (let ((.def_46 (* (- (/ 465936255648601 1125899906842624)) r2))) (let ((.def_47 (* (- (/ 393231763821699 1125899906842624)) r1))) (let ((.def_48 (* (- (/ 1383830923531217 9007199254740992)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 2994261938437 562949953421312))))) (let ((.def_51 (or b2 b1 .def_50))) (let ((.def_52 (* (- (/ 6967911305382625 9007199254740992)) r3))) (let ((.def_53 (* (/ 814904402958117 562949953421312) r2))) (let ((.def_54 (* (- (/ 3271632465745707 2251799813685248)) r1))) (let ((.def_55 (* (- (/ 1050098841300551 2251799813685248)) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 2118662771957279 9007199254740992)))) (let ((.def_58 (or b0 b3 .def_57))) (let ((.def_59 (* (/ 2564804181622869 4503599627370496) r3))) (let ((.def_60 (* (- (/ 3581689706637341 4503599627370496)) r2))) (let ((.def_61 (* (- (/ 569734044968549 1125899906842624)) r1))) (let ((.def_62 (* (/ 323901903248051 2251799813685248) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 232531242439533 2251799813685248)))) (let ((.def_65 (or .def_43 .def_35 .def_64))) (let ((.def_66 (* (- (/ 5761356409583189 9007199254740992)) r3))) (let ((.def_67 (* (/ 617033866949925 281474976710656) r2))) (let ((.def_68 (* (/ 1579646934232507 2251799813685248) r1))) (let ((.def_69 (* (- (/ 781767332476545 1125899906842624)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 1664889334042751 1125899906842624)))) (let ((.def_72 (or .def_35 b2 .def_71))) (let ((.def_73 (* (- (/ 4501158253563905 4503599627370496)) r3))) (let ((.def_74 (* (/ 2239214060143459 4503599627370496) r2))) (let ((.def_75 (* (/ 3246829348785 1125899906842624) r1))) (let ((.def_76 (* (- (/ 1960786890492999 4503599627370496)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 1309856502226093 9007199254740992))))) (let ((.def_79 (or .def_6 b2 .def_78))) (let ((.def_80 (* (/ 1800538916952403 9007199254740992) r3))) (let ((.def_81 (* (- (/ 5097523392792115 9007199254740992)) r2))) (let ((.def_82 (* (/ 1449727247625973 4503599627370496) r1))) (let ((.def_83 (* (/ 108319680040803 1125899906842624) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 1253993972534721 4503599627370496)))) (let ((.def_86 (or b2 b1 .def_85))) (let ((.def_87 (* (- (/ 2826468636878465 4503599627370496)) r3))) (let ((.def_88 (* (/ 3050666804015895 9007199254740992) r2))) (let ((.def_89 (* (- (/ 1820213977704073 1125899906842624)) r1))) (let ((.def_90 (* (/ 4886151216526015 9007199254740992) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (/ 1218900646216153 9007199254740992)))) (let ((.def_93 (or .def_43 b0 .def_92))) (let ((.def_94 (* (/ 4245403422206517 4503599627370496) r3))) (let ((.def_95 (* (/ 1377255390247297 9007199254740992) r2))) (let ((.def_96 (* (- (/ 6399703636944019 4503599627370496)) r1))) (let ((.def_97 (* (/ 2454013075661857 4503599627370496) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (/ 818576575022411 1125899906842624)))) (let ((.def_100 (not b2))) (let ((.def_101 (or .def_100 b3 .def_99))) (let ((.def_102 (* (- (/ 1285676397428045 9007199254740992)) r3))) (let ((.def_103 (* (- (/ 6069116285722799 9007199254740992)) r2))) (let ((.def_104 (* (/ 2593913090515893 9007199254740992) r1))) (let ((.def_105 (* (- (/ 3631086512938223 2251799813685248)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 1659244259674519 4503599627370496))))) (let ((.def_108 (or b1 b3 .def_107))) (let ((.def_109 (* (/ 2094121496528561 4503599627370496) r3))) (let ((.def_110 (* (- (/ 53396062536675 281474976710656)) r2))) (let ((.def_111 (* (- (/ 4607978411457191 4503599627370496)) r1))) (let ((.def_112 (* (/ 472085565092371 9007199254740992) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 100583356048369 1125899906842624)))) (let ((.def_115 (or .def_100 .def_6 .def_114))) (let ((.def_116 (* (/ 531957098840395 4503599627370496) r3))) (let ((.def_117 (* (- (/ 5245454343777853 9007199254740992)) r2))) (let ((.def_118 (* (- (/ 2141828499262077 2251799813685248)) r1))) (let ((.def_119 (* (- (/ 1150585294417125 1125899906842624)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 2839152881721549 4503599627370496))))) (let ((.def_122 (or .def_6 .def_43 .def_121))) (let ((.def_123 (* (/ 2162229656928229 4503599627370496) r3))) (let ((.def_124 (* (- (/ 7385413673582417 4503599627370496)) r2))) (let ((.def_125 (* (- (/ 112099237787851 281474976710656)) r1))) (let ((.def_126 (* (/ 2924676197645285 4503599627370496) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (/ 2042273697844179 9007199254740992)))) (let ((.def_129 (or b2 .def_6 .def_128))) (let ((.def_130 (* (/ 124937845671599 9007199254740992) r3))) (let ((.def_131 (* (/ 2983283058542197 4503599627370496) r2))) (let ((.def_132 (* (/ 58001990531845 9007199254740992) r1))) (let ((.def_133 (* (/ 8981741416900007 9007199254740992) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (/ 737770761366837 562949953421312)))) (let ((.def_136 (or b1 .def_6 .def_135))) (let ((.def_137 (* (- (/ 2620792757511997 9007199254740992)) r3))) (let ((.def_138 (* (/ 2359088546606331 2251799813685248) r2))) (let ((.def_139 (* (- (/ 555624903992403 281474976710656)) r1))) (let ((.def_140 (* (- (/ 131027072464741 9007199254740992)) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (/ 1095807381104439 9007199254740992)))) (let ((.def_143 (or .def_6 b2 .def_142))) (let ((.def_144 (* (- (/ 3865097420554699 9007199254740992)) r3))) (let ((.def_145 (* (/ 4285698878329543 4503599627370496) r2))) (let ((.def_146 (* (- (/ 2083909795306297 2251799813685248)) r1))) (let ((.def_147 (* (- (/ 2578609493518145 2251799813685248)) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (- (/ 140765886824825 2251799813685248))))) (let ((.def_150 (or .def_35 b2 .def_149))) (let ((.def_151 (* (- (/ 2668903686813279 1125899906842624)) r3))) (let ((.def_152 (* (/ 2364561243473637 4503599627370496) r2))) (let ((.def_153 (* (/ 1013498241699573 4503599627370496) r1))) (let ((.def_154 (* (- (/ 265253465356939 140737488355328)) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (- (/ 2159497847464519 4503599627370496))))) (let ((.def_157 (or b2 b3 .def_156))) (let ((.def_158 (* (- (/ 4943128192373253 4503599627370496)) r3))) (let ((.def_159 (* (/ 715599182561789 4503599627370496) r2))) (let ((.def_160 (* (- (/ 3739362047525707 2251799813685248)) r1))) (let ((.def_161 (* (/ 262219513727755 140737488355328) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (/ 2592838307627215 4503599627370496)))) (let ((.def_164 (or .def_43 .def_6 .def_163))) (let ((.def_165 (* (- (/ 1290622271560165 2251799813685248)) r3))) (let ((.def_166 (* (/ 1084174280529389 9007199254740992) r2))) (let ((.def_167 (* (/ 1433127177435245 9007199254740992) r1))) (let ((.def_168 (* (/ 403882572380879 2251799813685248) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (/ 741760109070737 4503599627370496)))) (let ((.def_171 (or b3 .def_35 .def_170))) (let ((.def_172 (and .def_171 .def_164 .def_157 .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_93 .def_86 .def_79 .def_72 .def_65 .def_58 .def_51 .def_44 .def_36 .def_28 .def_21 .def_14 .def_7))) .def_172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)