(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b0 () Bool)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 3386122983502879 2251799813685248)) r3))) (let ((.def_1 (* (/ 2530110143237677 2251799813685248) r2))) (let ((.def_2 (* (/ 1184716577528971 1125899906842624) r1))) (let ((.def_3 (* (/ 4120559687704445 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 335819357748149 281474976710656)))) (let ((.def_6 (* (- (/ 451434393084455 2251799813685248)) r3))) (let ((.def_7 (* (- (/ 1706213053358449 4503599627370496)) r2))) (let ((.def_8 (* (/ 587097036487069 4503599627370496) r1))) (let ((.def_9 (* (/ 4786817499815251 2251799813685248) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 8206335901361441 9007199254740992)))) (let ((.def_12 (not b2))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (/ 919499551918995 562949953421312) r3))) (let ((.def_15 (* (- (/ 829576509903123 1125899906842624)) r2))) (let ((.def_16 (* (/ 741141953421705 1125899906842624) r1))) (let ((.def_17 (* (/ 3727316449159523 9007199254740992) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 8802569307281387 9007199254740992)))) (let ((.def_20 (* (- (/ 1197202727912155 1125899906842624)) r3))) (let ((.def_21 (* (/ 7814411971256719 2251799813685248) r2))) (let ((.def_22 (* (- (/ 1406069697765835 1125899906842624)) r1))) (let ((.def_23 (* (/ 2575766391842061 1125899906842624) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 3692735561403611 2251799813685248)))) (let ((.def_26 (or b2 .def_25 .def_19))) (let ((.def_27 (* (- (/ 7161865495810697 9007199254740992)) r3))) (let ((.def_28 (* (- (/ 5474312609491059 9007199254740992)) r2))) (let ((.def_29 (* (/ 2234966515230263 9007199254740992) r1))) (let ((.def_30 (* (- (/ 8493260608927903 4503599627370496)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (- (/ 7345509735435365 9007199254740992))))) (let ((.def_33 (* (/ 311148308083217 562949953421312) r3))) (let ((.def_34 (* (- (/ 1233888110330197 9007199254740992)) r2))) (let ((.def_35 (* (- (/ 2381541489726017 2251799813685248)) r1))) (let ((.def_36 (* (- (/ 284160044518023 281474976710656)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 8737282673481113 9007199254740992))))) (let ((.def_39 (or b3 .def_38 .def_32))) (let ((.def_40 (* (- (/ 1464745954863709 4503599627370496)) r3))) (let ((.def_41 (* (/ 83212895686025 562949953421312) r2))) (let ((.def_42 (* (/ 4009430019835 8796093022208) r1))) (let ((.def_43 (* (/ 1614064358154611 1125899906842624) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 2348519935989179 2251799813685248)))) (let ((.def_46 (* (- (/ 1076291718015189 4503599627370496)) r3))) (let ((.def_47 (* (- (/ 3457069459094599 9007199254740992)) r2))) (let ((.def_48 (* (/ 2388051842999847 9007199254740992) r1))) (let ((.def_49 (* (- (/ 7268761198042581 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 2938350040339011 4503599627370496))))) (let ((.def_52 (not b1))) (let ((.def_53 (or .def_52 .def_51 .def_45))) (let ((.def_54 (* (/ 1351869860253681 2251799813685248) r3))) (let ((.def_55 (* (- (/ 882854228028203 4503599627370496)) r2))) (let ((.def_56 (* (- (/ 1636600210048133 1125899906842624)) r1))) (let ((.def_57 (* (- (/ 2270367686559707 2251799813685248)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (- (/ 2311298890751269 4503599627370496))))) (let ((.def_60 (* (/ 1578719987514995 1125899906842624) r3))) (let ((.def_61 (* (- (/ 45670673401859 70368744177664)) r2))) (let ((.def_62 (* (- (/ 3950422540324067 4503599627370496)) r1))) (let ((.def_63 (* (- (/ 1133660146252391 4503599627370496)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 3793190550676131 9007199254740992))))) (let ((.def_66 (or b2 .def_65 .def_59))) (let ((.def_67 (* (/ 700353970675239 4503599627370496) r3))) (let ((.def_68 (* (/ 7047630099523111 9007199254740992) r2))) (let ((.def_69 (* (/ 176979246597117 9007199254740992) r1))) (let ((.def_70 (* (/ 546642717989091 9007199254740992) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 2828449344383043 4503599627370496)))) (let ((.def_73 (* (/ 6038886274625913 9007199254740992) r3))) (let ((.def_74 (* (- (/ 2277818842309971 2251799813685248)) r2))) (let ((.def_75 (* (- (/ 161498231096019 281474976710656)) r1))) (let ((.def_76 (* (/ 1319051071622071 2251799813685248) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 1151511914924595 4503599627370496))))) (let ((.def_79 (or b2 .def_78 .def_72))) (let ((.def_80 (* (/ 3049922226242091 4503599627370496) r3))) (let ((.def_81 (* (/ 1158625357023591 2251799813685248) r2))) (let ((.def_82 (* (/ 476163612231521 2251799813685248) r1))) (let ((.def_83 (* (- (/ 6037192632510145 9007199254740992)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 2763363285828273 4503599627370496)))) (let ((.def_86 (* (- (/ 3572119534244549 9007199254740992)) r3))) (let ((.def_87 (* (/ 463170699425763 281474976710656) r2))) (let ((.def_88 (* (/ 343583409399055 9007199254740992) r1))) (let ((.def_89 (* (/ 7036799332038509 9007199254740992) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 8961777863713913 9007199254740992)))) (let ((.def_92 (not b3))) (let ((.def_93 (or .def_92 .def_91 .def_85))) (let ((.def_94 (* (/ 366613646788693 4503599627370496) r3))) (let ((.def_95 (* (- (/ 1129461107158611 1125899906842624)) r2))) (let ((.def_96 (* (/ 1071700918329563 9007199254740992) r1))) (let ((.def_97 (* (- (/ 4681521547809909 9007199254740992)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 1632585857777561 9007199254740992))))) (let ((.def_100 (* (/ 1853914514803549 1125899906842624) r3))) (let ((.def_101 (* (- (/ 7080812824459223 4503599627370496)) r2))) (let ((.def_102 (* (/ 1097529359574885 562949953421312) r1))) (let ((.def_103 (* (- (/ 4582194722436951 2251799813685248)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 558558860541709 4503599627370496))))) (let ((.def_106 (or .def_92 .def_105 .def_99))) (let ((.def_107 (* (/ 7393304350601169 4503599627370496) r3))) (let ((.def_108 (* (/ 1486800053487405 2251799813685248) r2))) (let ((.def_109 (* (- (/ 3544398784911525 2251799813685248)) r1))) (let ((.def_110 (* (- (/ 1484533186736253 4503599627370496)) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (/ 271438777981991 9007199254740992)))) (let ((.def_113 (* (- (/ 6596405952950905 9007199254740992)) r3))) (let ((.def_114 (* (- (/ 3491524204458819 9007199254740992)) r2))) (let ((.def_115 (* (/ 1127345748482821 1125899906842624) r1))) (let ((.def_116 (* (/ 181870239335691 9007199254740992) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (- (/ 38989229017011 1125899906842624))))) (let ((.def_119 (or b1 .def_118 .def_112))) (let ((.def_120 (* (- (/ 1444522346246317 9007199254740992)) r3))) (let ((.def_121 (* (- (/ 8082670831473579 9007199254740992)) r2))) (let ((.def_122 (* (- (/ 5585039656974571 4503599627370496)) r1))) (let ((.def_123 (* (/ 3900124904284737 9007199254740992) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (- (/ 4962988471538541 9007199254740992))))) (let ((.def_126 (* (/ 7632952024835167 9007199254740992) r3))) (let ((.def_127 (* (- (/ 5338279231494899 9007199254740992)) r2))) (let ((.def_128 (* (/ 5033917178114085 9007199254740992) r1))) (let ((.def_129 (* (- (/ 264749064976227 1125899906842624)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 504077969247601 2251799813685248)))) (let ((.def_132 (or b3 .def_131 .def_125))) (let ((.def_133 (* (/ 195309248260887 4503599627370496) r3))) (let ((.def_134 (* (- (/ 2573525702540849 4503599627370496)) r2))) (let ((.def_135 (* (- (/ 4263212547683073 4503599627370496)) r1))) (let ((.def_136 (* (- (/ 1779246844191823 4503599627370496)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 2870824160084155 4503599627370496))))) (let ((.def_139 (* (- (/ 1286463429887129 2251799813685248)) r3))) (let ((.def_140 (* (/ 2746601242828319 2251799813685248) r2))) (let ((.def_141 (* (- (/ 2687035916421793 4503599627370496)) r1))) (let ((.def_142 (* (/ 1090979542868907 2251799813685248) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (/ 2202200373589555 9007199254740992)))) (let ((.def_145 (not b0))) (let ((.def_146 (or .def_145 .def_144 .def_138))) (let ((.def_147 (* (- (/ 817413973139783 4503599627370496)) r3))) (let ((.def_148 (* (/ 272027440396987 9007199254740992) r2))) (let ((.def_149 (* (/ 2743289301072107 4503599627370496) r1))) (let ((.def_150 (* (- (/ 2907213265465769 2251799813685248)) r0))) (let ((.def_151 (+ .def_150 .def_149 .def_148 .def_147))) (let ((.def_152 (<= .def_151 (- (/ 195316121246735 1125899906842624))))) (let ((.def_153 (* (/ 4749218647508325 2251799813685248) r3))) (let ((.def_154 (* (/ 3180420756383049 1125899906842624) r2))) (let ((.def_155 (* (- (/ 2523255526757553 9007199254740992)) r1))) (let ((.def_156 (* (/ 2886372726752013 1125899906842624) r0))) (let ((.def_157 (+ .def_156 .def_155 .def_154 .def_153))) (let ((.def_158 (<= .def_157 (/ 1987994882088319 562949953421312)))) (let ((.def_159 (or b1 .def_158 .def_152))) (let ((.def_160 (and .def_159 .def_146 .def_132 .def_119 .def_106 .def_93 .def_79 .def_66 .def_53 .def_39 .def_26 .def_13))) .def_160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
