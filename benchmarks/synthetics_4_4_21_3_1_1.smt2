(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 400996783425283 2251799813685248) r3))) (let ((.def_1 (* (- (/ 2409707625892277 9007199254740992)) r2))) (let ((.def_2 (* (/ 4033716921579867 4503599627370496) r1))) (let ((.def_3 (* (- (/ 2181048905214563 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 4376955711057455 9007199254740992)))) (let ((.def_6 (not b3))) (let ((.def_7 (or b0 .def_6 .def_5))) (let ((.def_8 (* (- (/ 548594270476085 1125899906842624)) r3))) (let ((.def_9 (* (- (/ 4307034777900979 4503599627370496)) r2))) (let ((.def_10 (* (/ 1927996428698497 4503599627370496) r1))) (let ((.def_11 (* (- (/ 1105488593863927 1125899906842624)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 261710524920069 562949953421312))))) (let ((.def_14 (not b2))) (let ((.def_15 (or .def_6 .def_14 .def_13))) (let ((.def_16 (* (/ 4393034903371307 4503599627370496) r3))) (let ((.def_17 (* (/ 337992046289053 4503599627370496) r2))) (let ((.def_18 (* (- (/ 2100725547227635 4503599627370496)) r1))) (let ((.def_19 (* (/ 3899879333780435 4503599627370496) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (/ 4715645663676641 4503599627370496)))) (let ((.def_22 (or b0 .def_14 .def_21))) (let ((.def_23 (* (/ 8227471632286723 9007199254740992) r3))) (let ((.def_24 (* (/ 156842373226447 2251799813685248) r2))) (let ((.def_25 (* (- (/ 2620844805711157 2251799813685248)) r1))) (let ((.def_26 (* (/ 1389993669909423 9007199254740992) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (/ 3855458096543841 9007199254740992)))) (let ((.def_29 (or b1 .def_14 .def_28))) (let ((.def_30 (* (- (/ 7468287402358569 9007199254740992)) r3))) (let ((.def_31 (* (- (/ 313380967783679 1125899906842624)) r2))) (let ((.def_32 (* (- (/ 4534070059054659 2251799813685248)) r1))) (let ((.def_33 (* (/ 2182892717729301 9007199254740992) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (- (/ 8369727100735261 9007199254740992))))) (let ((.def_36 (not b0))) (let ((.def_37 (or .def_36 b3 .def_35))) (let ((.def_38 (* (/ 4967104381504215 9007199254740992) r3))) (let ((.def_39 (* (/ 568771954563733 4503599627370496) r2))) (let ((.def_40 (* (- (/ 2401214284846631 4503599627370496)) r1))) (let ((.def_41 (* (- (/ 4775401508373379 9007199254740992)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 126069450914573 4503599627370496)))) (let ((.def_44 (or b2 .def_36 .def_43))) (let ((.def_45 (* (/ 2929628038361113 2251799813685248) r3))) (let ((.def_46 (* (- (/ 444073643590853 562949953421312)) r2))) (let ((.def_47 (* (/ 1395779897459453 2251799813685248) r1))) (let ((.def_48 (* (- (/ 2333823920600707 4503599627370496)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 4076559959924767 4503599627370496)))) (let ((.def_51 (not b1))) (let ((.def_52 (or .def_14 .def_51 .def_50))) (let ((.def_53 (* (/ 35905528174157 281474976710656) r3))) (let ((.def_54 (* (- (/ 2061183849095731 1125899906842624)) r2))) (let ((.def_55 (* (/ 1080331724136685 4503599627370496) r1))) (let ((.def_56 (* (- (/ 6122838763242133 9007199254740992)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 105310375757645 281474976710656))))) (let ((.def_59 (or b1 b3 .def_58))) (let ((.def_60 (* (/ 4277251563788555 9007199254740992) r3))) (let ((.def_61 (* (/ 4191411963928533 4503599627370496) r2))) (let ((.def_62 (* (- (/ 1395153997720733 2251799813685248)) r1))) (let ((.def_63 (* (- (/ 3953799368568911 9007199254740992)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 5203155733658875 9007199254740992)))) (let ((.def_66 (or b3 .def_14 .def_65))) (let ((.def_67 (* (- (/ 1290576597647473 2251799813685248)) r3))) (let ((.def_68 (* (- (/ 4260712214965861 4503599627370496)) r2))) (let ((.def_69 (* (- (/ 1175035112025189 9007199254740992)) r1))) (let ((.def_70 (* (/ 3252148605494673 2251799813685248) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 4762339586868569 9007199254740992)))) (let ((.def_73 (or .def_51 b0 .def_72))) (let ((.def_74 (* (/ 48685317349115 281474976710656) r3))) (let ((.def_75 (* (- (/ 1189837167256931 4503599627370496)) r2))) (let ((.def_76 (* (- (/ 6800554534489621 4503599627370496)) r1))) (let ((.def_77 (* (/ 1185385675016373 1125899906842624) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 3690080964893743 9007199254740992)))) (let ((.def_80 (or b3 .def_51 .def_79))) (let ((.def_81 (* (/ 2040891603869311 4503599627370496) r3))) (let ((.def_82 (* (- (/ 8736225956253935 9007199254740992)) r2))) (let ((.def_83 (* (- (/ 1073475935307753 4503599627370496)) r1))) (let ((.def_84 (* (/ 114443888565533 4503599627370496) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 306466013438533 9007199254740992))))) (let ((.def_87 (or .def_6 .def_36 .def_86))) (let ((.def_88 (* (- (/ 1870890588523255 4503599627370496)) r3))) (let ((.def_89 (* (/ 2250114276390079 4503599627370496) r2))) (let ((.def_90 (* (- (/ 8984528102396025 9007199254740992)) r1))) (let ((.def_91 (* (- (/ 3297430365074025 2251799813685248)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 1510801289938725 2251799813685248))))) (let ((.def_94 (or b0 b2 .def_93))) (let ((.def_95 (* (/ 133591707757907 2251799813685248) r3))) (let ((.def_96 (* (- (/ 5046918944596405 4503599627370496)) r2))) (let ((.def_97 (* (- (/ 879706768819349 562949953421312)) r1))) (let ((.def_98 (* (/ 282213138065203 2251799813685248) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 6459838880061741 9007199254740992))))) (let ((.def_101 (or .def_6 b2 .def_100))) (let ((.def_102 (* (- (/ 5027991046532025 9007199254740992)) r3))) (let ((.def_103 (* (- (/ 1115892544708801 9007199254740992)) r2))) (let ((.def_104 (* (- (/ 2075901975933525 1125899906842624)) r1))) (let ((.def_105 (* (/ 1067407292052835 2251799813685248) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 1676896723237521 9007199254740992))))) (let ((.def_108 (or .def_6 .def_14 .def_107))) (let ((.def_109 (* (/ 4915016569505263 9007199254740992) r3))) (let ((.def_110 (* (- (/ 81400256108503 562949953421312)) r2))) (let ((.def_111 (* (- (/ 3156282721031829 9007199254740992)) r1))) (let ((.def_112 (* (- (/ 1305182029709271 9007199254740992)) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 1833046313601767 9007199254740992)))) (let ((.def_115 (or b1 b2 .def_114))) (let ((.def_116 (* (- (/ 1462351513844423 4503599627370496)) r3))) (let ((.def_117 (* (/ 1487506585050313 4503599627370496) r2))) (let ((.def_118 (* (/ 1200523790067 4503599627370496) r1))) (let ((.def_119 (* (- (/ 1234125482686747 2251799813685248)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 311621944793639 9007199254740992))))) (let ((.def_122 (or b3 b1 .def_121))) (let ((.def_123 (* (- (/ 791900893912145 2251799813685248)) r3))) (let ((.def_124 (* (- (/ 4270896262818401 9007199254740992)) r2))) (let ((.def_125 (* (- (/ 1670592162165729 1125899906842624)) r1))) (let ((.def_126 (* (- (/ 1174289138030817 1125899906842624)) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (- (/ 8491860741232849 9007199254740992))))) (let ((.def_129 (or .def_51 .def_6 .def_128))) (let ((.def_130 (* (/ 4227387523055075 4503599627370496) r3))) (let ((.def_131 (* (- (/ 3449327548903509 9007199254740992)) r2))) (let ((.def_132 (* (/ 3150618386553881 4503599627370496) r1))) (let ((.def_133 (* (- (/ 3746561191400915 9007199254740992)) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (/ 8847274857766955 9007199254740992)))) (let ((.def_136 (or b0 b3 .def_135))) (let ((.def_137 (* (- (/ 3189820060688053 4503599627370496)) r3))) (let ((.def_138 (* (/ 429799095392957 562949953421312) r2))) (let ((.def_139 (* (- (/ 1022177547199965 562949953421312)) r1))) (let ((.def_140 (* (- (/ 816777550358315 1125899906842624)) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (- (/ 73083701082097 140737488355328))))) (let ((.def_143 (or b3 b2 .def_142))) (let ((.def_144 (* (- (/ 526702194398619 2251799813685248)) r3))) (let ((.def_145 (* (- (/ 758292165946967 4503599627370496)) r2))) (let ((.def_146 (* (- (/ 7088358916026421 4503599627370496)) r1))) (let ((.def_147 (* (- (/ 496186121342579 562949953421312)) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (- (/ 5488898419818617 9007199254740992))))) (let ((.def_150 (or b3 b2 .def_149))) (let ((.def_151 (and .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_37 .def_29 .def_22 .def_15 .def_7))) .def_151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)