type Lohnsteuer2023Big = {
	/**  Stand: 2023-11-16 14:40 */
	/**  ITZBund Berlin  */
	/**   EINGABEPARAMETER   */
	/**  1, wenn die Anwendung des Faktorverfahrens gewählt wurden (nur in Steuerklasse IV)  */
	af: number,
	/**  in VKAPA und VMT enthaltene Entschädigungen nach §24 Nummer 1 EStG
		 sowie tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen
		 (§ 19a Absatz 4 EStG) in Cent  */
	ENTSCH: number,
	/**  eingetragener Faktor mit drei Nachkommastellen  */
	f: number,
	/**  Dem Arbeitgeber mitgeteilte Zahlungen des Arbeitnehmers zur privaten
		 Kranken- bzw. Pflegeversicherung im Sinne des §10 Abs. 1 Nr. 3 EStG 2010
		 als Monatsbetrag in Cent (der Wert ist inabhängig vom Lohnzahlungszeitraum immer
		 als Monatsbetrag anzugeben). */
	PKPV: number,
	/**  Krankenversicherung:
		 0 = gesetzlich krankenversicherte Arbeitnehmer
		 1 = ausschließlich privat krankenversicherte Arbeitnehmer OHNE Arbeitgeberzuschuss
		 2 = ausschließlich privat krankenversicherte Arbeitnehmer MIT Arbeitgeberzuschuss  */
	PKV: number,
	/**  1, wenn bei der sozialen Pflegeversicherung die Besonderheiten in Sachsen zu berücksichtigen sind bzw.
			zu berücksichtigen wären, sonst 0.  */
	PVS: number,
	/**  1, wenn er der Arbeitnehmer den Zuschlag zur sozialen Pflegeversicherung
			zu zahlen hat, sonst 0.  */
	PVZ: number,
	/**  In JRE4 enthaltene Entschädigungen nach § 24 Nummer 1 EStG und zu besteuernde
		 Vorteile bei Vermögensbeteiligungen (§ 19a Absatz 4 EStG in Cent  */
	JRE4ENT: number,
	/**  In SONSTB enthaltene Entschädigungen nach § 24 Nummer 1 EStG sowie nicht
		 tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen in Cent  */
	SONSTENT: number,
	/**   AUSGABEPARAMETER   */
	/**  Bemessungsgrundlage fuer die Kirchenlohnsteuer in Cents  */
	BK: number,
	/**  Bemessungsgrundlage der sonstigen Bezüge (ohne Vergütung für mehrjährige Tätigkeit)
		 für die Kirchenlohnsteuer in Cent.
		 Hinweis: Negativbeträge, die aus nicht zu besteuernden Vorteilen bei
		 Vermögensbeteiligungen (§ 19a Absatz 1 Satz 4 EStG) resultieren, mindern BK
		 (maximal bis 0). Der Sonderausgabenabzug für tatsächlich erbrachte Vorsorgeaufwendungen
		 im Rahmen der Veranlagung zur Einkommensteuer bleibt unberührt.  */
	BKS: number,
	/**  Bemessungsgrundlage der Vergütung für mehrjährige Tätigkeit und der tarifermäßigt
		 zu besteuernden Vorteile bei Vermögensbeteiligungen für die Kirchenlohnsteuer in Cent   */
	BKV: number,
	/**  Fuer den Lohnzahlungszeitraum einzubehaltende Lohnsteuer in Cents  */
	LSTLZZ: number,
	/**  Fuer den Lohnzahlungszeitraum einzubehaltender Solidaritaetszuschlag
		 in Cents  */
	SOLZLZZ: number,
	/**  Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit in Cent.
		 Hinweis: Negativbeträge, die aus nicht zu besteuernden Vorteilen bei Vermögensbeteiligungen
		 (§ 19a Absatz 1 Satz 4 EStG) resultieren, mindern SOLZLZZ (maximal bis 0). Der
		 Sonderausgabenabzug für tatsächlich erbrachte Vorsorgeaufwendungen im Rahmen der
		 Veranlagung zur Einkommensteuer bleibt unberührt.  */
	SOLZS: number,
	/**  Solidaritätszuschlag für die Vergütung für mehrjährige Tätigkeit und der tarifermäßigt
		 zu besteuernden Vorteile bei Vermögensbeteiligungen in Cent  */
	SOLZV: number,
	/**  Lohnsteuer für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit und ohne
		 tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen) in Cent
		 Hinweis: Negativbeträge, die aus nicht zu besteuernden Vorteilen bei Vermögensbeteiligungen
		 (§ 19a Absatz 1 Satz 4 EStG) resultieren, mindern LSTLZZ (maximal bis 0). Der
		 Sonderausgabenabzug für tatsächlich erbrachte Vorsorgeaufwendungen im Rahmen der
		 Veranlagung zur Einkommensteuer bleibt unberührt.  */
	STS: number,
	/**  Lohnsteuer für die Vergütung für mehrjährige Tätigkeit und der tarifermäßigt zu besteuernden
		 Vorteile bei Vermögensbeteiligungen in Cent  */
	STV: number,
	/**  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers zur
		 privaten Basis-Krankenversicherung und privaten Pflege-Pflichtversicherung (ggf. auch
		 die Mindestvorsorgepauschale) in Cent beim laufenden Arbeitslohn. Für Zwecke der Lohn-
		 steuerbescheinigung sind die einzelnen Ausgabewerte außerhalb des eigentlichen Lohn-
		 steuerbescheinigungsprogramms zu addieren; hinzuzurechnen sind auch die Ausgabewerte
		 VKVSONST  */
	VKVLZZ: number,
	/**  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers
		 zur privaten Basis-Krankenversicherung und privaten Pflege-Pflichtversicherung (ggf.
		 auch die Mindestvorsorgepauschale) in Cent bei sonstigen Bezügen. Der Ausgabewert kann
		 auch negativ sein. Für tarifermäßigt zu besteuernde Vergütungen für mehrjährige
		 Tätigkeiten enthält der PAP keinen entsprechenden Ausgabewert.  */
	VKVSONST: number,
	/**   AUSGABEPARAMETER DBA   */
	/**  Verbrauchter Freibetrag bei Berechnung des laufenden Arbeitslohns, in Cent  */
	VFRB: number,
	/**  Verbrauchter Freibetrag bei Berechnung des voraussichtlichen Jahresarbeitslohns, in Cent  */
	VFRBS1: number,
	/**  Verbrauchter Freibetrag bei Berechnung der sonstigen Bezüge, in Cent  */
	VFRBS2: number,
	/**  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA Türkei verfügbares ZVE über
		dem Grundfreibetrag bei der Berechnung des laufenden Arbeitslohns, in Cent  */
	WVFRB: number,
	/**  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA Türkei verfügbares ZVE über dem Grundfreibetrag
		bei der Berechnung des voraussichtlichen Jahresarbeitslohns, in Cent  */
	WVFRBO: number,
	/**  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA Türkei verfügbares ZVE
		über dem Grundfreibetrag bei der Berechnung der sonstigen Bezüge, in Cent  */
	WVFRBM: number,
	/**   INTERNE FELDER   */
	/**  Altersentlastungsbetrag nach Alterseinkünftegesetz in €,
		 Cent (2 Dezimalstellen)  */
	ALTE: number,
	/**  Arbeitnehmer-Pauschbetrag in EURO  */
	ANP: number,
	/**  Auf den Lohnzahlungszeitraum entfallender Anteil von Jahreswerten
		 auf ganze Cents abgerundet  */
	ANTEIL1: number,
	/**  Bemessungsgrundlage für Altersentlastungsbetrag in €, Cent
		 (2 Dezimalstellen)  */
	BMG: number,
	/**  Beitragsbemessungsgrenze in der gesetzlichen Krankenversicherung
		und der sozialen Pflegeversicherung in Euro  */
	BBGKVPV: number,
	/**   Nach Programmablaufplan 2019  */
	bd: number,
	/**  allgemeine Beitragsbemessungsgrenze in der allgemeinen Renten-versicherung in Euro  */
	BBGRV: number,
	/**  Differenz zwischen ST1 und ST2 in EURO  */
	DIFF: number,
	/**  Entlastungsbetrag für Alleinerziehende in Euro  */
	EFA: number,
	/**  Versorgungsfreibetrag in €, Cent (2 Dezimalstellen)  */
	FVB: number,
	/**  Versorgungsfreibetrag in €, Cent (2 Dezimalstellen) für die Berechnung
		 der Lohnsteuer für den sonstigen Bezug  */
	FVBSO: number,
	/**  Zuschlag zum Versorgungsfreibetrag in EURO  */
	FVBZ: number,
	/**  Zuschlag zum Versorgungsfreibetrag in EURO fuer die Berechnung
		 der Lohnsteuer beim sonstigen Bezug  */
	FVBZSO: number,
	/**  Grundfreibetrag in Euro  */
	GFB: number,
	/**  Maximaler Altersentlastungsbetrag in €  */
	HBALTE: number,
	/**  Massgeblicher maximaler Versorgungsfreibetrag in €  */
	HFVB: number,
	/**  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €,Cent
		 (2 Dezimalstellen)  */
	HFVBZ: number,
	/**  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €, Cent
		 (2 Dezimalstellen) für die Berechnung der Lohnsteuer für den
		 sonstigen Bezug  */
	HFVBZSO: number,
	/**  Nummer der Tabellenwerte fuer Versorgungsparameter  */
	J: number,
	/**  Jahressteuer nach § 51a EStG, aus der Solidaritaetszuschlag und
		 Bemessungsgrundlage fuer die Kirchenlohnsteuer ermittelt werden in EURO  */
	JBMG: number,
	/**  Auf einen Jahreslohn hochgerechneter LZZFREIB in €, Cent
		 (2 Dezimalstellen)  */
	JLFREIB: number,
	/**  Auf einen Jahreslohn hochgerechnete LZZHINZU in €, Cent
		 (2 Dezimalstellen)  */
	JLHINZU: number,
	/**  Jahreswert, dessen Anteil fuer einen Lohnzahlungszeitraum in
		 UPANTEIL errechnet werden soll in Cents  */
	JW: number,
	/**  Nummer der Tabellenwerte fuer Parameter bei Altersentlastungsbetrag  */
	K: number,
	/**  Merker für Berechnung Lohnsteuer für mehrjährige Tätigkeit.
		 0 = normale Steuerberechnung
		 1 = Steuerberechnung für mehrjährige Tätigkeit
		 2 = entfällt  */
	KENNVMT: number,
	/**  Summe der Freibetraege fuer Kinder in EURO  */
	KFB: number,
	/**  Beitragssatz des Arbeitgebers zur Krankenversicherung  */
	KVSATZAG: number,
	/**  Beitragssatz des Arbeitnehmers zur Krankenversicherung  */
	KVSATZAN: number,
	/**  Kennzahl fuer die Einkommensteuer-Tabellenart:
		  1 = Grundtabelle
		  2 = Splittingtabelle  */
	KZTAB: number,
	/**  Jahreslohnsteuer in EURO  */
	LSTJAHR: number,
	/**  Zwischenfelder der Jahreslohnsteuer in Cent  */
	LST1: number,
	LST2: number,
	LST3: number,
	LSTOSO: number,
	LSTSO: number,
	/**  Mindeststeuer fuer die Steuerklassen V und VI in EURO  */
	MIST: number,
	/**  Beitragssatz des Arbeitgebers zur Pflegeversicherung  */
	PVSATZAG: number,
	/**  Beitragssatz des Arbeitnehmers zur Pflegeversicherung  */
	PVSATZAN: number,
	/**  Beitragssatz des Arbeitnehmers in der allgemeinen gesetzlichen Rentenversicherung (4 Dezimalstellen)   */
	RVSATZAN: number,
	/**  Rechenwert in Gleitkommadarstellung  */
	RW: number,
	/**  Sonderausgaben-Pauschbetrag in EURO  */
	SAP: number,
	/**  Freigrenze fuer den Solidaritaetszuschlag in EURO  */
	SOLZFREI: number,
	/**  Solidaritaetszuschlag auf die Jahreslohnsteuer in EURO, C (2 Dezimalstellen)  */
	SOLZJ: number,
	/**  Zwischenwert fuer den Solidaritaetszuschlag auf die Jahreslohnsteuer
		 in EURO, C (2 Dezimalstellen)  */
	SOLZMIN: number,
	/**  Neu ab 2021: Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung der Freigrenze beim Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit) in Euro  */
	SOLZSBMG: number,
	/**  Neu ab 2021: Zu versteuerndes Einkommen für die Ermittlung der Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung der Freigrenze beim Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit) in Euro, Cent (2 Dezimalstellen)  */
	SOLZSZVE: number,
	/**  Neu ab 2021: Bemessungsgrundlage des Solidaritätszuschlags für die Prüfung der Freigrenze beim Solidaritätszuschlag für die Vergütung für mehrjährige Tätigkeit in Euro  */
	SOLZVBMG: number,
	/**  Tarifliche Einkommensteuer in EURO  */
	ST: number,
	/**  Tarifliche Einkommensteuer auf das 1,25-fache ZX in EURO  */
	ST1: number,
	/**  Tarifliche Einkommensteuer auf das 0,75-fache ZX in EURO  */
	ST2: number,
	/**  Zwischenfeld zur Ermittlung der Steuer auf Vergütungen für mehrjährige Tätigkeit  */
	STOVMT: number,
	/**  Teilbetragssatz der Vorsorgepauschale für die Rentenversicherung (2 Dezimalstellen)  */
	TBSVORV: number,
	/**  Bemessungsgrundlage fuer den Versorgungsfreibetrag in Cents  */
	VBEZB: number,
	/**  Bemessungsgrundlage für den Versorgungsfreibetrag in Cent für
		 den sonstigen Bezug  */
	VBEZBSO: number,
	/**  Hoechstbetrag der Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C  */
	VHB: number,
	/**  Vorsorgepauschale in EURO, C (2 Dezimalstellen)  */
	VSP: number,
	/**  Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C  */
	VSPN: number,
	/**  Zwischenwert 1 bei der Berechnung der Vorsorgepauschale nach
		 dem Alterseinkuenftegesetz in EURO, C (2 Dezimalstellen)  */
	VSP1: number,
	/**  Zwischenwert 2 bei der Berechnung der Vorsorgepauschale nach
		 dem Alterseinkuenftegesetz in EURO, C (2 Dezimalstellen)  */
	VSP2: number,
	/**  Vorsorgepauschale mit Teilbeträgen für die gesetzliche Kranken- und
		 soziale Pflegeversicherung nach fiktiven Beträgen oder ggf. für die
		 private Basiskrankenversicherung und private Pflege-Pflichtversicherung
		 in Euro, Cent (2 Dezimalstellen)  */
	VSP3: number,
	/**  Erster Grenzwert in Steuerklasse V/VI in Euro  */
	W1STKL5: number,
	/**  Zweiter Grenzwert in Steuerklasse V/VI in Euro  */
	W2STKL5: number,
	/**  Dritter Grenzwert in Steuerklasse V/VI in Euro  */
	W3STKL5: number,
	/**  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 2 EStG in EURO  */
	VSPMAX1: number,
	/**  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 3 EStG in EURO  */
	VSPMAX2: number,
	/**  Vorsorgepauschale nach § 10c Abs. 2 Satz 2 EStG vor der Hoechstbetragsberechnung
		 in EURO, C (2 Dezimalstellen)  */
	VSPO: number,
	/**  Fuer den Abzug nach § 10c Abs. 2 Nrn. 2 und 3 EStG verbleibender
		 Rest von VSPO in EURO, C (2 Dezimalstellen)  */
	VSPREST: number,
	/**  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 1 EStG
		 in EURO, C (2 Dezimalstellen)  */
	VSPVOR: number,
	/**  Zu versteuerndes Einkommen gem. § 32a Abs. 1 und 2 EStG €, C
		 (2 Dezimalstellen)  */
	X: number,
	/**  gem. § 32a Abs. 1 EStG (6 Dezimalstellen)  */
	Y: number,
	/**  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)
		 nach Abzug der Freibeträge nach § 39 b Abs. 2 Satz 3 und 4.  */
	ZRE4: number,
	/**  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)  */
	ZRE4J: number,
	/**  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)
		 nach Abzug des Versorgungsfreibetrags und des Alterentlastungsbetrags
		 zur Berechnung der Vorsorgepauschale in €, Cent (2 Dezimalstellen)  */
	ZRE4VP: number,
	/**  Feste Tabellenfreibeträge (ohne Vorsorgepauschale) in €, Cent
		 (2 Dezimalstellen)  */
	ZTABFB: number,
	/**  Auf einen Jahreslohn hochgerechnetes (VBEZ abzueglich FVB) in
		 EURO, C (2 Dezimalstellen)  */
	ZVBEZ: number,
	/**  Auf einen Jahreslohn hochgerechnetes VBEZ in €, C (2 Dezimalstellen)  */
	ZVBEZJ: number,
	/**  Zu versteuerndes Einkommen in €, C (2 Dezimalstellen)  */
	ZVE: number,
	/**  Zwischenfelder zu X fuer die Berechnung der Steuer nach § 39b
		 Abs. 2 Satz 7 EStG in €  */
	ZX: number,
	ZZX: number,
	HOCH: number,
	VERGL: number,
	/**  Jahreswert der berücksichtigten Beiträge zur privaten Basis-Krankenversicherung und
		 privaten Pflege-Pflichtversicherung (ggf. auch die Mindestvorsorgepauschale) in Cent.  */
	VKV: number,
	KRV: number,
	KVZ: number,
	LZZ: number,
	RE4: number,
	VBEZ: number,
	LZZFREIB: number,
	LZZHINZU: number,
	ZKF: number,
	STKL: number,
	VMT: number,
	VKAPA: number,
	VERGL1: number,
	R: number,
	ZMVB: number,
	SONSTB: number,
	MBV: number,
	JRE4: number,
	JVBEZ: number,
	VBS: number,
	STERBE: number,
	JFREIB: number,
	JHINZU: number
};
/**  Zuweisung von Werten für bestimmte Sozialversicherungsparameter  PAP Seite 15  */
export function MPARA(obj: Lohnsteuer2023Big): void {
	if (obj.KRV < 2) { /**  &lt; = <  */
		if (obj.KRV == 0) {
			obj.BBGRV = 87600; /**  Geändert für 2023  */
		}
		else {
			obj.BBGRV = 85200; /**  Geändert für 2023  */
		}
		obj.RVSATZAN = 0.093; /**  Neu 2019  */
		obj.TBSVORV = 1.00; /**  Geändert für 2023 */
	}
	obj.BBGKVPV = 59850; /**  Geändert für 2023  */
	obj.bd = 2; /**  Neu 2019  */
	obj.KVSATZAN = obj.KVZ / obj.bd / 100 + 0.07; /**  Neu 2019  */
	obj.KVSATZAG = 0.008 + 0.07; /**  Geändert für 2023 */
	if (obj.PVS == 1) {
		obj.PVSATZAN = 0.02025; /**  Neu 2019  */
		obj.PVSATZAG = 0.01025; /**  Neu 2019  */
	}
	else {
		obj.PVSATZAN = 0.01525; /**  Neu 2019  */
		obj.PVSATZAG = 0.01525; /**  Neu 2019  */
	}
	if (obj.PVZ == 1) {
		obj.PVSATZAN = obj.PVSATZAN + 0.0035; /**   geändert für 2022  */
	}
	/**  Anfang Geändert für 2023  */
	obj.W1STKL5 = 12485;
	obj.W2STKL5 = 31404;
	obj.W3STKL5 = 222260;
	obj.GFB = 10908;
	obj.SOLZFREI = 17543;
	/**  Ende Geändert für 2023  */
}
/**  Ermittlung des Jahresarbeitslohns nach § 39 b Abs. 2 Satz 2 EStG, PAP Seite 16  */
export function MRE4JL(obj: Lohnsteuer2023Big): void {
	if (obj.LZZ == 1) {
		obj.ZRE4J = obj.RE4 / 100;
		obj.ZVBEZJ = obj.VBEZ / 100;
		obj.JLFREIB = obj.LZZFREIB / 100;
		obj.JLHINZU = obj.LZZHINZU / 100;
	}
	else {
		if (obj.LZZ == 2) {
			obj.ZRE4J = obj.RE4 * 12 / 100;
			obj.ZVBEZJ = obj.VBEZ * 12 / 100;
			obj.JLFREIB = obj.LZZFREIB * 12 / 100;
			obj.JLHINZU = obj.LZZHINZU * 12 / 100;
		}
		else {
			if (obj.LZZ == 3) {
				obj.ZRE4J = obj.RE4 * 360 / 700;
				obj.ZVBEZJ = obj.VBEZ * 360 / 700;
				obj.JLFREIB = obj.LZZFREIB * 360 / 700;
				obj.JLHINZU = obj.LZZHINZU * 360 / 700;
			}
			else {
				obj.ZRE4J = obj.RE4 * 360 / 100;
				obj.ZVBEZJ = obj.VBEZ * 360 / 100;
				obj.JLFREIB = obj.LZZFREIB * 360 / 100;
				obj.JLHINZU = obj.LZZHINZU * 360 / 100;
			}
		}
	}
	if (obj.af == 0) {
		obj.f = 1;
	}
}
/**  Ermittlung des Jahresarbeitslohns nach Abzug der Freibeträge nach § 39 b Abs. 2 Satz 3 und 4 EStG, PAP Seite 20  */
export function MRE4ABZ(obj: Lohnsteuer2023Big): void {
	obj.ZRE4 = obj.ZRE4J - obj.FVB - obj.ALTE - obj.JLFREIB + obj.JLHINZU;
	if (obj.ZRE4 < 0) {
		obj.ZRE4 = 0;
	}
	obj.ZRE4VP = obj.ZRE4J;
	if (obj.KENNVMT == 2) {
		obj.ZRE4VP = obj.ZRE4VP - obj.ENTSCH / 100;
	}
	obj.ZVBEZ = obj.ZVBEZJ - obj.FVB;
	if (obj.ZVBEZ < 0) {
		obj.ZVBEZ = 0;
	}
}
/**  Berechnung fuer laufende Lohnzahlungszeitraueme Seite 21 */
export function MBERECH(obj: Lohnsteuer2023Big): void {
	MZTABFB(obj);
	obj.VFRB = (obj.ANP + obj.FVB + obj.FVBZ) * 100;
	MLSTJAHR(obj);
	obj.WVFRB = (obj.ZVE - obj.GFB) * 100;
	if (obj.WVFRB < 0) { /**  WVFRB < 0  */
		obj.WVFRB = 0;
	}
	obj.LSTJAHR = obj.ST * obj.f;
	UPLSTLZZ(obj);
	UPVKVLZZ(obj);
	if (obj.ZKF > 0) { /**  ZKF > 0  */
		obj.ZTABFB = obj.ZTABFB + obj.KFB;
		MRE4ABZ(obj);
		MLSTJAHR(obj);
		obj.JBMG = obj.ST * obj.f;
	}
	else {
		obj.JBMG = obj.LSTJAHR;
	}
	MSOLZ(obj);
}
/**  Ermittlung der festen Tabellenfreibeträge (ohne Vorsorgepauschale), PAP Seite 22  */
export function MZTABFB(obj: Lohnsteuer2023Big): void {
	obj.ANP = 0;
	if (obj.ZVBEZ >= 0 && obj.ZVBEZ < obj.FVBZ) {
		obj.FVBZ = obj.ZVBEZ;
	}
	if (obj.STKL < 6) {
		if (obj.ZVBEZ > 0) {
			if (obj.ZVBEZ - obj.FVBZ < 102) {
				obj.ANP = obj.ZVBEZ - obj.FVBZ;
			}
			else {
				obj.ANP = 102;
			}
		}
	}
	else {
		obj.FVBZ = 0;
		obj.FVBZSO = 0;
	}
	if (obj.STKL < 6) {
		if (obj.ZRE4 > obj.ZVBEZ) {
			if (obj.ZRE4 - obj.ZVBEZ < 1200) {
				obj.ANP = obj.ANP + obj.ZRE4 - obj.ZVBEZ;
			}
			else {
				obj.ANP = obj.ANP + 1200;
			}
		}
	}
	obj.KZTAB = 1;
	if (obj.STKL == 1) {
		obj.SAP = 36;
		obj.KFB = obj.ZKF * 8952; /**  Geändert für 2023  */
	}
	else {
		if (obj.STKL == 2) {
			obj.EFA = 4008; /**  Geändert für 2022  */
			obj.SAP = 36;
			obj.KFB = obj.ZKF * 8952; /**  Geändert für 2023  */
		}
		else {
			if (obj.STKL == 3) {
				obj.KZTAB = 2;
				obj.SAP = 36;
				obj.KFB = obj.ZKF * 8952; /**  Geändert für 2023  */
			}
			else {
				if (obj.STKL == 4) {
					obj.SAP = 36;
					obj.KFB = obj.ZKF * 4476; /**  Geändert für 2023  */
				}
				else {
					if (obj.STKL == 5) {
						obj.SAP = 36;
						obj.KFB = 0;
					}
					else {
						obj.KFB = 0;
					}
				}
			}
		}
	}
	obj.ZTABFB = obj.EFA + obj.ANP + obj.SAP + obj.FVBZ;
}
/**  Ermittlung Jahreslohnsteuer, PAP Seite 23  */
export function MLSTJAHR(obj: Lohnsteuer2023Big): void {
	UPEVP(obj);
	if (obj.KENNVMT != 1) {
		obj.ZVE = obj.ZRE4 - obj.ZTABFB - obj.VSP;
		UPMLST(obj);
	}
	else {
		obj.ZVE = obj.ZRE4 - obj.ZTABFB - obj.VSP - obj.VMT / 100 - obj.VKAPA / 100;
		if (obj.ZVE < 0) {
			obj.ZVE = (obj.ZVE + obj.VMT / 100 + obj.VKAPA / 100) / 5;
			UPMLST(obj);
			obj.ST = obj.ST * 5;
		}
		else {
			UPMLST(obj);
			obj.STOVMT = obj.ST;
			obj.ZVE = obj.ZVE + (obj.VMT + obj.VKAPA) / 500;
			UPMLST(obj);
			obj.ST = (obj.ST - obj.STOVMT) * 5 + obj.STOVMT;
		}
	}
}
/**  PAP Seite 24  */
export function UPVKVLZZ(obj: Lohnsteuer2023Big): void {
	UPVKV(obj);
	obj.JW = obj.VKV;
	UPANTEIL(obj);
	obj.VKVLZZ = obj.ANTEIL1;
}
/**  PAP Seite 24  */
export function UPVKV(obj: Lohnsteuer2023Big): void {
	if (obj.PKV > 0) {
		if (obj.VSP2 > obj.VSP3) {
			obj.VKV = obj.VSP2 * 100;
		}
		else {
			obj.VKV = obj.VSP3 * 100;
		}
	}
	else {
		obj.VKV = 0;
	}
}
/**  PAP Seite 25  */
export function UPLSTLZZ(obj: Lohnsteuer2023Big): void {
	obj.JW = obj.LSTJAHR * 100;
	UPANTEIL(obj);
	obj.LSTLZZ = obj.ANTEIL1;
}
/**  Ermittlung der Jahreslohnsteuer aus dem Einkommensteuertarif. PAP Seite 26  */
export function UPMLST(obj: Lohnsteuer2023Big): void {
	if (obj.ZVE < 1) {
		obj.ZVE = 0;
		obj.X = 0;
	}
	else {
		obj.X = obj.ZVE / obj.KZTAB;
	}
	if (obj.STKL < 5) {
		/**  Änderung für 2023  */
		UPTAB23(obj);
	}
	else {
		MST5_6(obj);
	}
}
/**  	Vorsorgepauschale (§ 39b Absatz 2 Satz 5 Nummer 3 und Absatz 4 EStG) PAP Seite 27   */
export function UPEVP(obj: Lohnsteuer2023Big): void {
	if (obj.KRV > 1) { /**  &lt; = < &gt; = >  */
		obj.VSP1 = 0;
	}
	else {
		if (obj.ZRE4VP > obj.BBGRV) {
			obj.ZRE4VP = obj.BBGRV;
		}
		obj.VSP1 = obj.TBSVORV * obj.ZRE4VP;
		obj.VSP1 = obj.VSP1 * obj.RVSATZAN;
	}
	obj.VSP2 = obj.ZRE4VP * 0.12;
	if (obj.STKL == 3) {
		obj.VHB = 3000;
	}
	else {
		obj.VHB = 1900;
	}
	if (obj.VSP2 > obj.VHB) {
		obj.VSP2 = obj.VHB;
	}
	obj.VSPN = obj.VSP1 + obj.VSP2;
	MVSP(obj);
	if (obj.VSPN > obj.VSP) {
		obj.VSP = obj.VSPN;
	}
}
/**  Vorsorgepauschale (§39b Abs. 2 Satz 5 Nr 3 EStG) Vergleichsberechnung fuer Guenstigerpruefung, PAP Seite 28  */
export function MVSP(obj: Lohnsteuer2023Big): void {
	if (obj.ZRE4VP > obj.BBGKVPV) {
		obj.ZRE4VP = obj.BBGKVPV;
	}
	if (obj.PKV > 0) {
		if (obj.STKL == 6) {
			obj.VSP3 = 0;
		}
		else {
			obj.VSP3 = obj.PKPV * 12 / 100;
			if (obj.PKV == 2) {
				obj.VSP3 = obj.VSP3 - obj.ZRE4VP * (obj.KVSATZAG + obj.PVSATZAG);
			}
		}
	}
	else {
		obj.VSP3 = obj.ZRE4VP * (obj.KVSATZAN + obj.PVSATZAN);
	}
	obj.VSP = obj.VSP3 + obj.VSP1;
}
/**  Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs. 2 Satz 7 EStG), PAP Seite 29  */
export function MST5_6(obj: Lohnsteuer2023Big): void {
	obj.ZZX = obj.X;
	if (obj.ZZX > obj.W2STKL5) {
		obj.ZX = obj.W2STKL5;
		UP5_6(obj);
		if (obj.ZZX > obj.W3STKL5) {
			obj.ST = obj.ST + (obj.W3STKL5 - obj.W2STKL5) * 0.42;
			obj.ST = obj.ST + (obj.ZZX - obj.W3STKL5) * 0.45;
		}
		else {
			obj.ST = obj.ST + (obj.ZZX - obj.W2STKL5) * 0.42;
		}
	}
	else {
		obj.ZX = obj.ZZX;
		UP5_6(obj);
		if (obj.ZZX > obj.W1STKL5) {
			obj.VERGL = obj.ST;
			obj.ZX = obj.W1STKL5;
			UP5_6(obj);
			obj.HOCH = obj.ST + (obj.ZZX - obj.W1STKL5) * 0.42; /**  Neuer Wert 2014  */
			if (obj.HOCH < obj.VERGL1) {
				obj.ST = obj.HOCH;
			}
			else {
				obj.ST = obj.VERGL;
			}
		}
	}
}
/**  Unterprogramm zur Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs. 2 Satz 7 EStG), PAP Seite 30  */
export function UP5_6(obj: Lohnsteuer2023Big): void {
	obj.X = obj.ZX * 1.25;
	/**  Änderung für 2023  */
	UPTAB23(obj);
	obj.ST1 = obj.ST;
	obj.X = obj.ZX * 0.75;
	/**  Änderung für 2023  */
	UPTAB23(obj);
	obj.ST2 = obj.ST;
	obj.DIFF = (obj.ST1 - obj.ST2) * 2;
	obj.MIST = obj.ZX * 0.14;
	if (obj.MIST > obj.DIFF) {
		obj.ST = obj.MIST;
	}
	else {
		obj.ST = obj.DIFF;
	}
}
/**  Solidaritaetszuschlag, PAP Seite 31  */
export function MSOLZ(obj: Lohnsteuer2023Big): void {
	obj.SOLZFREI = obj.SOLZFREI * obj.KZTAB;
	if (obj.JBMG > obj.SOLZFREI) {
		obj.SOLZJ = obj.JBMG * 5.5 / 100;
		obj.SOLZMIN = (obj.JBMG - obj.SOLZFREI) * 11.9 / 100; /**  Änderung für 2021  */
		if (obj.SOLZMIN < obj.SOLZJ) {
			obj.SOLZJ = obj.SOLZMIN;
		}
		obj.JW = obj.SOLZJ * 100;
		UPANTEIL(obj);
		obj.SOLZLZZ = obj.ANTEIL1;
	}
	else {
		obj.SOLZLZZ = 0;
	}
	if (obj.R > 0) {
		obj.JW = obj.JBMG * 100;
		UPANTEIL(obj);
		obj.BK = obj.ANTEIL1;
	}
	else {
		obj.BK = 0;
	}
}
/**  Anteil von Jahresbetraegen fuer einen LZZ (§ 39b Abs. 2 Satz 9 EStG), PAP Seite 32  */
export function UPANTEIL(obj: Lohnsteuer2023Big): void {
	if (obj.LZZ == 1) {
		obj.ANTEIL1 = obj.JW;
	}
	else {
		if (obj.LZZ == 2) {
			obj.ANTEIL1 = obj.JW / 12;
		}
		else {
			if (obj.LZZ == 3) {
				obj.ANTEIL1 = obj.JW * 7 / 360;
			}
			else {
				obj.ANTEIL1 = obj.JW / 360;
			}
		}
	}
}
/**  Neu für 2022, PAP Seite 34  */
export function STSMIN(obj: Lohnsteuer2023Big): void {
	if (obj.STS < 0) { /**  STS < 0  */
		if (obj.MBV == 0) {
			obj.LSTLZZ = obj.LSTLZZ + obj.STS;
			if (obj.LSTLZZ < 0) { /**   LSTLZZ < 0  */
				obj.LSTLZZ = 0;
			}
			obj.SOLZLZZ = obj.SOLZLZZ + obj.STS * 5.5 / 100;
			if (obj.SOLZLZZ < 0) { /**   SOLZLZZ < 0  */
				obj.SOLZLZZ = 0;
			}
			obj.BK = obj.BK + obj.STS;
			if (obj.BK < 0) { /**   BK < 0  */
				obj.BK = 0;
			}
		}
		obj.STS = 0;
		obj.SOLZS = 0;
	}
	else {
		MSOLZSTS(obj);
	}
	if (obj.R > 0) {
		obj.BKS = obj.STS;
	}
	else {
		obj.BKS = 0;
	}
}
/**  Berechnung des SolZ auf sonstige Bezüge, PAP Seite 35, Neu ab 2021  */
export function MSOLZSTS(obj: Lohnsteuer2023Big): void {
	if (obj.ZKF > 0) { /**  ZKF > 0  */
		obj.SOLZSZVE = obj.ZVE - obj.KFB;
	}
	else {
		obj.SOLZSZVE = obj.ZVE;
	}
	if (obj.SOLZSZVE < 1) { /**  SOLZSZVE < 1  */
		obj.SOLZSZVE = 0;
		obj.X = 0;
	}
	else {
		obj.X = obj.SOLZSZVE / obj.KZTAB;
	}
	if (obj.STKL < 5) { /**  STKL < 5  */
		/**  Änderung für 2023  */
		UPTAB23(obj);
	}
	else {
		MST5_6(obj);
	}
	obj.SOLZSBMG = obj.ST * obj.f;
	if (obj.SOLZSBMG > obj.SOLZFREI) { /**  SOLZSBMG > SOLZFREI  */
		obj.SOLZS = obj.STS * 5.5 / 100;
	}
	else {
		obj.SOLZS = 0;
	}
}
/**  Komplett Neu 2020  */
/**  Tarifliche Einkommensteuer §32a EStG, PAP Seite 39  */
export function UPTAB23(obj: Lohnsteuer2023Big): void {
	if (obj.X < obj.GFB + 1) {
		obj.ST = 0;
	}
	else {
		if (obj.X < 15999) { /**  Geändert für 2023  */
			obj.Y = (obj.X - obj.GFB) / 10000;
			obj.RW = obj.Y * 979.18; /**  Geändert für 2023  */
			obj.RW = obj.RW + 1400;
			obj.ST = obj.RW * obj.Y;
		}
		else {
			if (obj.X < 62810) { /**  Geändert für 2023  */
				obj.Y = (obj.X - 15999) / 10000; /**  Geändert für 2023   */
				obj.RW = obj.Y * 192.59; /**  Geändert für 2023  */
				obj.RW = obj.RW + 2397;
				obj.RW = obj.RW * obj.Y;
				obj.ST = obj.RW + 966.53; /**  Geändert für 2023  */
			}
			else {
				if (obj.X < 277826) { /**  Geändert für 2022  */
					obj.ST = obj.X * 0.42 - 9972.98; /**  Geändert für 2023  */
				}
				else {
					obj.ST = obj.X * 0.45 - 18307.73; /**  Geändert für 2023  */
				}
			}
		}
	}
	obj.ST = obj.ST * obj.KZTAB;
}