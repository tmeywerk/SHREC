(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun b0 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 757698108148215 2251799813685248) r3))) (let ((.def_1 (* (- (/ 7834293083927171 9007199254740992)) r2))) (let ((.def_2 (* (- (/ 806626748825807 4503599627370496)) r1))) (let ((.def_3 (* (- (/ 648666741186745 562949953421312)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1209755755400509 2251799813685248))))) (let ((.def_6 (* (/ 4172420327799713 4503599627370496) r3))) (let ((.def_7 (* (- (/ 1912235683253779 4503599627370496)) r2))) (let ((.def_8 (* (/ 853252186365481 1125899906842624) r1))) (let ((.def_9 (* (/ 264499849924315 9007199254740992) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 2675469895388515 4503599627370496)))) (let ((.def_12 (or b1 .def_11 .def_5))) (let ((.def_13 (* (/ 834167259645105 562949953421312) r3))) (let ((.def_14 (* (- (/ 2355598203216865 1125899906842624)) r2))) (let ((.def_15 (* (- (/ 599872361408413 4503599627370496)) r1))) (let ((.def_16 (* (- (/ 1224338187723781 4503599627370496)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (- (/ 3128219287765277 9007199254740992))))) (let ((.def_19 (* (- (/ 459754073162147 1125899906842624)) r3))) (let ((.def_20 (* (/ 8252798223462293 9007199254740992) r2))) (let ((.def_21 (* (/ 953283921619701 562949953421312) r1))) (let ((.def_22 (* (- (/ 578093855155561 4503599627370496)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 8070253580431123 9007199254740992)))) (let ((.def_25 (not b1))) (let ((.def_26 (or .def_25 .def_24 .def_18))) (let ((.def_27 (* (/ 4286511788119267 2251799813685248) r3))) (let ((.def_28 (* (- (/ 2228963424479287 2251799813685248)) r2))) (let ((.def_29 (* (- (/ 8416660786280201 4503599627370496)) r1))) (let ((.def_30 (* (- (/ 3610536806754393 9007199254740992)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (- (/ 5280862597925181 9007199254740992))))) (let ((.def_33 (* (- (/ 355682933209 70368744177664)) r3))) (let ((.def_34 (* (- (/ 744334169046145 9007199254740992)) r2))) (let ((.def_35 (* (/ 819845821538599 1125899906842624) r1))) (let ((.def_36 (* (- (/ 1917537369385017 4503599627370496)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (/ 1016137279041973 9007199254740992)))) (let ((.def_39 (not b0))) (let ((.def_40 (or .def_39 .def_38 .def_32))) (let ((.def_41 (* (- (/ 5222119629926455 9007199254740992)) r3))) (let ((.def_42 (* (/ 5401841993623217 4503599627370496) r2))) (let ((.def_43 (* (- (/ 98136929169873 2251799813685248)) r1))) (let ((.def_44 (* (/ 1376651428806301 4503599627370496) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 2276164076270245 2251799813685248)))) (let ((.def_47 (* (- (/ 5866162741691905 9007199254740992)) r3))) (let ((.def_48 (* (/ 1567731033489887 2251799813685248) r2))) (let ((.def_49 (* (- (/ 6053733011520553 9007199254740992)) r1))) (let ((.def_50 (* (/ 4017082915379531 9007199254740992) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 257746081479757 2251799813685248))))) (let ((.def_53 (or b2 .def_52 .def_46))) (let ((.def_54 (* (/ 8114291397656033 4503599627370496) r3))) (let ((.def_55 (* (- (/ 2547016646547713 9007199254740992)) r2))) (let ((.def_56 (* (- (/ 7784419616547193 9007199254740992)) r1))) (let ((.def_57 (* (- (/ 5248119538324831 9007199254740992)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 334324039773173 562949953421312)))) (let ((.def_60 (* (- (/ 94423343378075 4503599627370496)) r3))) (let ((.def_61 (* (/ 815113278648965 9007199254740992) r2))) (let ((.def_62 (* (- (/ 403312213652389 1125899906842624)) r1))) (let ((.def_63 (* (- (/ 852991887248365 1125899906842624)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 671824813852007 1125899906842624))))) (let ((.def_66 (not b3))) (let ((.def_67 (or .def_66 .def_65 .def_59))) (let ((.def_68 (* (- (/ 1261332432190963 1125899906842624)) r3))) (let ((.def_69 (* (- (/ 2543106647728583 4503599627370496)) r2))) (let ((.def_70 (* (/ 4596276829824339 4503599627370496) r1))) (let ((.def_71 (* (- (/ 6588039872277909 9007199254740992)) r0))) (let ((.def_72 (+ .def_71 .def_70 .def_69 .def_68))) (let ((.def_73 (<= .def_72 (- (/ 548375922759111 9007199254740992))))) (let ((.def_74 (* (- (/ 1130420458767089 1125899906842624)) r3))) (let ((.def_75 (* (- (/ 1636665738703847 9007199254740992)) r2))) (let ((.def_76 (* (/ 146030445127217 140737488355328) r1))) (let ((.def_77 (* (- (/ 1793690210619791 9007199254740992)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 1480403503136291 9007199254740992))))) (let ((.def_80 (or .def_25 .def_79 .def_73))) (let ((.def_81 (* (- (/ 3244373770606433 4503599627370496)) r3))) (let ((.def_82 (* (/ 3125002197844383 2251799813685248) r2))) (let ((.def_83 (* (- (/ 322517200382211 9007199254740992)) r1))) (let ((.def_84 (* (/ 44392183819395 140737488355328) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 391618185737943 562949953421312)))) (let ((.def_87 (* (/ 5904708243036973 9007199254740992) r3))) (let ((.def_88 (* (- (/ 781247981417251 4503599627370496)) r2))) (let ((.def_89 (* (- (/ 996418240802759 9007199254740992)) r1))) (let ((.def_90 (* (- (/ 84138154467537 281474976710656)) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (- (/ 3961199319317 281474976710656))))) (let ((.def_93 (or b1 .def_92 .def_86))) (let ((.def_94 (* (/ 362059010228073 281474976710656) r3))) (let ((.def_95 (* (- (/ 1682283794785645 1125899906842624)) r2))) (let ((.def_96 (* (- (/ 2659770637446661 2251799813685248)) r1))) (let ((.def_97 (* (- (/ 5795629567981959 9007199254740992)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 6596978113757 4503599627370496))))) (let ((.def_100 (* (/ 2649331233770895 1125899906842624) r3))) (let ((.def_101 (* (/ 5780828838553097 9007199254740992) r2))) (let ((.def_102 (* (- (/ 2193721217675375 1125899906842624)) r1))) (let ((.def_103 (* (/ 754033631461615 4503599627370496) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (/ 3688510006774705 9007199254740992)))) (let ((.def_106 (or .def_39 .def_105 .def_99))) (let ((.def_107 (* (- (/ 548668049951331 2251799813685248)) r3))) (let ((.def_108 (* (/ 1337407660075595 4503599627370496) r2))) (let ((.def_109 (* (- (/ 2927208198965909 2251799813685248)) r1))) (let ((.def_110 (* (/ 3406380254783275 4503599627370496) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (- (/ 296491742702171 2251799813685248))))) (let ((.def_113 (* (- (/ 118165291053059 2251799813685248)) r3))) (let ((.def_114 (* (- (/ 315202956557527 562949953421312)) r2))) (let ((.def_115 (* (/ 715633226415933 562949953421312) r1))) (let ((.def_116 (* (/ 251324442094315 562949953421312) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (/ 609085583769851 1125899906842624)))) (let ((.def_119 (or b1 .def_118 .def_112))) (let ((.def_120 (* (/ 240373655866401 2251799813685248) r3))) (let ((.def_121 (* (- (/ 244995441630571 9007199254740992)) r2))) (let ((.def_122 (* (/ 3477489695847627 2251799813685248) r1))) (let ((.def_123 (* (- (/ 4859904928001023 2251799813685248)) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (/ 7677323157430827 9007199254740992)))) (let ((.def_126 (* (- (/ 3854638476149483 4503599627370496)) r3))) (let ((.def_127 (* (- (/ 7673907680209709 4503599627370496)) r2))) (let ((.def_128 (* (/ 576260300851243 562949953421312) r1))) (let ((.def_129 (* (- (/ 2423456188920017 4503599627370496)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (- (/ 1138399101119583 1125899906842624))))) (let ((.def_132 (or .def_25 .def_131 .def_125))) (let ((.def_133 (* (- (/ 7574085567682603 9007199254740992)) r3))) (let ((.def_134 (* (- (/ 8214804282676529 9007199254740992)) r2))) (let ((.def_135 (* (- (/ 3640930958367133 2251799813685248)) r1))) (let ((.def_136 (* (- (/ 1742978569938685 2251799813685248)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 1290940294563741 1125899906842624))))) (let ((.def_139 (* (- (/ 2761646985764217 2251799813685248)) r3))) (let ((.def_140 (* (- (/ 2535929082775649 2251799813685248)) r2))) (let ((.def_141 (* (- (/ 53898233012343 9007199254740992)) r1))) (let ((.def_142 (* (/ 6724222990703691 4503599627370496) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 3790928081072155 9007199254740992))))) (let ((.def_145 (not b2))) (let ((.def_146 (or .def_145 .def_144 .def_138))) (let ((.def_147 (* (/ 8085450093998795 9007199254740992) r3))) (let ((.def_148 (* (- (/ 2061078785181613 9007199254740992)) r2))) (let ((.def_149 (* (- (/ 3977983285178011 9007199254740992)) r1))) (let ((.def_150 (* (/ 1774300739445451 4503599627370496) r0))) (let ((.def_151 (+ .def_150 .def_149 .def_148 .def_147))) (let ((.def_152 (<= .def_151 (/ 2907511254527055 4503599627370496)))) (let ((.def_153 (* (- (/ 1732632955907725 9007199254740992)) r3))) (let ((.def_154 (* (/ 8326062458533097 9007199254740992) r2))) (let ((.def_155 (* (/ 125009714744993 2251799813685248) r1))) (let ((.def_156 (* (/ 892101763918731 1125899906842624) r0))) (let ((.def_157 (+ .def_156 .def_155 .def_154 .def_153))) (let ((.def_158 (<= .def_157 (/ 1699439948494923 2251799813685248)))) (let ((.def_159 (or .def_145 .def_158 .def_152))) (let ((.def_160 (* (/ 714481821858875 281474976710656) r3))) (let ((.def_161 (* (/ 7652049535310697 9007199254740992) r2))) (let ((.def_162 (* (- (/ 2390673156869649 4503599627370496)) r1))) (let ((.def_163 (* (- (/ 2094627029345409 1125899906842624)) r0))) (let ((.def_164 (+ .def_163 .def_162 .def_161 .def_160))) (let ((.def_165 (<= .def_164 (/ 6913439230762569 9007199254740992)))) (let ((.def_166 (* (- (/ 732240663266591 562949953421312)) r3))) (let ((.def_167 (* (/ 263921830691839 562949953421312) r2))) (let ((.def_168 (* (- (/ 5170767499121795 9007199254740992)) r1))) (let ((.def_169 (* (/ 1692752443505193 4503599627370496) r0))) (let ((.def_170 (+ .def_169 .def_168 .def_167 .def_166))) (let ((.def_171 (<= .def_170 (- (/ 1226409452899865 2251799813685248))))) (let ((.def_172 (or .def_25 .def_171 .def_165))) (let ((.def_173 (and .def_172 .def_159 .def_146 .def_132 .def_119 .def_106 .def_93 .def_80 .def_67 .def_53 .def_40 .def_26 .def_12))) .def_173)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
