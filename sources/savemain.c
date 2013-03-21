#include <iostream>
#include <stdlib.h>
#include <vector>
#include <string.h>
#include <string>
#include <sstream>
#include <fstream>


// le "epsilon" est consid�r� ici comme un di�se (#), caract�re r�serv�
#define epsilon "#"

using namespace std;


// structure permettant d'identifier pr�cisement une r�gle
// int ruleID : num�ro de la r�gle parmis les autres
// string ruleLetter : lettre correspondant � la r�gle
typedef struct RuleIdentificator {
    int ruleID;
    string ruleLetter;
} RuleIdentificator;


// prototypes
// fonctions connexes au sujet (debug, affichage traces...)
template <class type>
void printVector (vector<type> vect, string name = "");
void drawGrammar (vector<string> grammar, string name = "");
void printNewTraitmentRule (string ruleLetter, int ruleID);

// fonctions importantes
void readGrammarFile(vector<string> *grammar, string fileName); // !important
RuleIdentificator getDirectLeftRecursivity (vector<string> *grammar, string letter = ""); // !important
bool repareDirectLeftRecursivity (vector<string> *grammar, RuleIdentificator ri); // !important

bool repareDirectLeftRecursivityFromLetter (vector<string> *grammar, RuleIdentificator ri);
unsigned repareAllDirectLeftRecursivity (vector<string> *grammar);





// imprime le contenu entier d'un vecteur (type utilis� ici : string)
template <class type>
void printVector (const vector<type> *vect, string name) {
    cout << endl << " " << name << ":" << endl << endl ;
    for (size_t i = 0; i < vect->size(); i++)
        cout << "  |- V[" << i << "] = " << vect->at(i) << endl;
}


// dessine une grammaire selon le format EFREI (fleches, pipe...)
void drawGrammar (const vector<string> *grammar, string name) {
    unsigned ruleIDCounter = 0;
    bool nextArrow = false;

    if (grammar->empty()) {
        cout << endl << " Grammaire vide..." << endl;
        return;
    }

    cout << endl << " " << name << ":" << endl << endl ;
    cout << " 0. " << grammar->at(0) << " -> ";

    for (size_t i = 1; i < grammar->size(); i++) {
       if (grammar->at(i) == ";") {
           ruleIDCounter++;
           nextArrow = true;
           cout << endl << " " << ruleIDCounter << ". ";
           continue;
       }
       if (nextArrow) {
           cout << grammar->at(i) << " -> ";
           nextArrow = false;
       }
       else if (grammar->at(i) == "|")
           cout << " | ";
       else
           cout << grammar->at(i);
   }
   cout << endl;
}


// lit un fichier de grammaire
// SPECIFICATIONS DE FORMAT
// - chaque caract�res est s�par� d'un autre avec un espace blanc
// - pour une m�me r�gle concernant un seul non terminal, utilisez les pipes "|" pour les unions
// - s�parer chaque r�gle concernant un non terminal diff�rent du pr�c�dent par un point-virgule ";"
// - la fin de la grammaire se traduit par un aobase "@"
// - pour une meilleure lisibilit�, sauter une ligne pour chaque nouvelle r�gle incluant un nouveau non terminal

void readGrammarFile(vector<string> *grammar, string fileName) {
    try {
        if ((unsigned)strlen(fileName.c_str()) <= 0)
        // si le nom contient au moins un caract�re
            throw string("File " + fileName + " doesn't exist");

        // on cr�er le flux de lecture sur le fichier
        ifstream streamFile;
        streamFile.open(fileName.c_str());

        // on v�rifie la bonne ouverture
        if (!streamFile.is_open())
            throw string("Could not open the file " + fileName);

        string currentChar;
        do {
            streamFile >> currentChar;
            grammar->push_back(currentChar);
        } while (currentChar != "@");

        grammar->pop_back(); // on enleve le @ de fin

        // on referme le flux de lecture du fichier
        streamFile.close();

    // traitement s'il y a eu une erreur
    } catch (string e) {
        cerr << endl << " readGrammarFileError: " << e << endl;
        exit(1);
    }
}



vector<string> getPipedRulesInstructions (vector<string> *ruleGrammar) {
    vector<string> pipedInstr;
    string patternSplit = "";

     if (ruleGrammar->size() <= 1)
        return pipedInstr;

    // on met chaque union (instructions) de la regle dans une case d'un vecteur
    for (size_t i = 1; i < ruleGrammar->size(); i++) {
        if (ruleGrammar->at(i) == "|" || i + 1 == ruleGrammar->size()) {
            string lastLetter = (i + 1 >= ruleGrammar->size() && ruleGrammar->at(i) != "|") ? ruleGrammar->at(i) : "";
            pipedInstr.push_back(patternSplit + lastLetter);
            patternSplit = "";
        } else
            patternSplit += ruleGrammar->at(i);
    }
    return pipedInstr;
}





// fonction renvoyant le nombre d'occurences de "pattern" dans une regle "ruleGrammar"
// le motif doit toujours etre positionn� en premi�re position de chaque instruction pour etre comptabilis�
unsigned getNumberPatternRepetition (vector<string> pipedInstr, string pattern) {
    unsigned occCounter = 0; // compteur de motif

    // pour chaque instruction (union)...
    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        char *ptStr = strstr(pipedInstr[instr].c_str(), pattern.c_str()); // donne le pointeur sur la premiere occurence trouv�e
        if (ptStr && *ptStr == pipedInstr[instr][0]) // si l'occurence trouv�e est bien en premi�re position de l'instruction alors OK
            occCounter++;
    }
    return occCounter;
}





// fonction renvoyant la liste de toutes les instructions factoris�es (les betas) d'une regle
// parametres: le jeu d'instructions decoup� (vector), le motif qui factorise les instructions
vector<string> getFactorizableTerms (vector<string> pipedInstr, string pattern) {
    vector<string> factorizedTerms;

    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        if (pipedInstr[instr].substr(0, pattern.size()) == pattern) { // l'instruction actuelle contient le motif
            if (pipedInstr[instr].size() > pattern.size()) // l'instruction n'est pas termin�e, on va donc factoriser le reste
                factorizedTerms.push_back(pipedInstr[instr].substr(pattern.size(), pipedInstr[instr].size() - 1));

            // sinon, l'instruction est termin�, on place epsilon
            else
                factorizedTerms.push_back(epsilon);
        }
    }

    return factorizedTerms;
}





// fonction donnant les instructions ne contenant pas le motif qu'on veut factoriser
// cette fonction prend un jeu d'instruction d'une regle en param�tre et le motif qu'on souhaite factoriser
// elle renvoi un vecteur contenant les instructions concern�es
vector<string> getNonFactorizableTerms (vector<string> pipedInstr, string pattern) {
    vector<string> otherPatterns;

    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        if (pipedInstr[instr].substr(0, pattern.size()) != pattern)
            otherPatterns.push_back(pipedInstr[instr]);
    }

    return otherPatterns;
}






// fonction donnant le motif le plus pr�sent dans une expression de r�gle
// cette fonction prend en param�tre un vecteur contenant les instructions d'une regle
// en renvoi une chaine de caracteres representant le motif � factoriser
string getRuleLeftFactorizationPattern (vector<string> pipedInstr) {

    string currentPattern, globalPattern = "";
    unsigned currentNbRep = 0, globalNbRep = 0;

    // on cherche le plus grand motif commun � toutes les cases du vecteur des instructions
    for (size_t instr = 0; instr < pipedInstr.size(); instr++) { // on prend chaque instruction de la regle
        for (unsigned letter = 0; letter <= pipedInstr[instr].size(); letter++) { // pour chaque instruction on prend chaque caractere
            currentPattern = globalPattern + pipedInstr[instr][letter]; // on d�fini le nouveau motif
            currentNbRep = getNumberPatternRepetition(pipedInstr, currentPattern); // nombre de repetition pour ce nouveau motif..

            if (currentNbRep < globalNbRep) // si on est all� trop loin, on retourne le motif d'avant
                return globalPattern;

            globalNbRep = currentNbRep; // sinon on continu avec les valeurs actuelles
            globalPattern = currentPattern;
        } // endfor
    } // endfor

    return (globalNbRep <= 1) ? "" : globalPattern;
}




// fonction permettant de factoriser une grammaire � gauche
// fonction renvoyant vrai ou faux selon si elle a agit ou non
// elle prend une grammaire en param�tre
bool makeLeftFactorization (vector<string> *grammar) {
    if (grammar->size() < 2)
        return false;

    vector<string> rulesInstr, result_rules, grammar_copy;

    for (size_t i = 0; i < grammar->size(); i++) {
        grammar_copy.push_back(grammar->at(i));
    }

    string ruleLetter = grammar_copy[0];
    int rulePosition = 0;
    bool last = false;
    printVector(&grammar_copy, "la grammaire");

    for (size_t i = 0; i < grammar_copy.size(); i++) { // pour chaque r�gle, on applique
        cout << endl << " on arrive au i = " << i << " pou " << grammar_copy[i] << endl;
        cout << grammar_copy.size() << endl;
        if (grammar_copy[i] != ";" && i + 1 < grammar_copy.size() && !last) { // on est pas en fin de regle donc on insert les instructions
            if (i + 2 == (int)grammar_copy.size()) {
                rulesInstr.push_back(grammar_copy[i]);
                rulesInstr.push_back(grammar_copy[i+1]);
                last = true;
            }
            else {
                cout << " I NORMAL ICI = " << grammar_copy[i] << endl;
                rulesInstr.push_back(grammar_copy[i]);
            }
        }
        else { // on arrive en bout de regle, on traite la regle avant de passer � la suivante

            cout << " RULE LETTER = " << ruleLetter << endl << endl;

            vector<string> pipedInstr = getPipedRulesInstructions(&rulesInstr);
            string fPattern = getRuleLeftFactorizationPattern(pipedInstr);
            vector<string> nonFactorizableTerms = getNonFactorizableTerms(pipedInstr, fPattern); // beta
            vector<string> factorizableTerms = getFactorizableTerms(pipedInstr, fPattern); // alpha

            printVector(&rulesInstr, "INSTRUCTIONS");
            printVector(&pipedInstr, "PIPED INSTRUCTIONS");
            cout << endl << endl << "pattern = " << fPattern << endl << endl;
            printVector(&nonFactorizableTerms, "non factorisables terms");
            printVector(&factorizableTerms, "factorizable terms");

            result_rules.push_back(ruleLetter);

            for (unsigned p = 0; p < fPattern.size(); p++) { // on place le motif de factorisation � sa place
                stringstream ss; // on converti de char => string
                string letter;
                ss << fPattern[p];
                ss >> letter;
                result_rules.push_back(letter);
            }
            result_rules.push_back(ruleLetter + "'");

            for (size_t k = 0; k < nonFactorizableTerms.size(); k++) { // on ajoute la liste des termes non factorisables
                result_rules.push_back("|");
                result_rules.push_back(nonFactorizableTerms[k]);
            }

            result_rules.push_back(";");
            result_rules.push_back(ruleLetter + "'");
            for (size_t k = 0; k < factorizableTerms.size(); k++) { // on ajoute la liste des facteurs de alpha
                if (k > 0)
                    result_rules.push_back("|");
                result_rules.push_back(factorizableTerms[k]);
            }
            result_rules.push_back(";");

            int add = 1;
            printVector(&grammar_copy, "grammar_copy");
            cout << "grammar_copy[rulesInstr.size()] = " << grammar_copy[rulesInstr.size()] << endl;
            if (grammar_copy[rulesInstr.size()] != ";")
                add = 0;

            cout << endl << "suppression de 0 a " << rulesInstr.size() + add;
            printVector(grammar, "avant suppression");

            grammar->erase(grammar->begin(), grammar->begin() + rulesInstr.size() + add);

            printVector(&result_rules, "resultat temporaire");
            printVector(grammar, "grammar APRES");

            if (grammar->empty())
                break;
            else
                ruleLetter = grammar->at(1);
            cout << " RULE LETTER 2 " << ruleLetter;

            rulesInstr.clear();
        } // endif

    } // endfor

    grammar->insert(grammar->end(), result_rules.begin(), result_rules.end());

    drawGrammar(grammar, "nouvelle grammaire");
    printVector(&result_rules, "apres factorisation");
    return true;
}




// parcourt la grammaire � la recherche de la premi�re r�cursivit� gauche directe trouv�e
// le param�tre letter:string est facultatif et permet de ne detecter que les recursivit� d�es � cette lettre
// fonction retournant la position exacte de la r�gle qui pose probl�me ainsi que la lettre repr�sentant le non terminal recursif de la r�gle
RuleIdentificator getDirectLeftRecursivity (vector<string> *grammar, string letter) {
    cout << endl << endl << " -------- NOUVELLE ANALYSE RECURSIVITE GAUCHE DIRECTE --------" << endl << endl;

    RuleIdentificator ri, ri0; // identificateurs de position de recursivite (ri pour si il y a recursivite, ri0 pour sinon)
    ri0.ruleID = -1;
    ri0.ruleLetter = "";

    ri.ruleID = -1;
    ri.ruleLetter = letter;

    if (grammar->size() < 2)
        return ri0;

    // on parcourt la grammaire
    string firstLetter = grammar->at(0);
    string secondLetter = grammar->at(1);
    ri.ruleID++;

    // on parcourt la grammaire car. par car. et on compare la premi�re lettre (non terminal) aux premi�res lettre de chaque conditions
    for (size_t i = 2; i < grammar->size(); i++) {
        cout << endl << " i = " << i << endl;
        cout << " fL = " << firstLetter << " et sL = " << secondLetter << endl;
        ri.ruleLetter = firstLetter;

        // cas 1: on a equivalence des caract�res donc r�cursivit� gauche directe
        if (firstLetter == secondLetter) {
            if (letter != "" && firstLetter == letter) {
                cout << " " << firstLetter << " = " << secondLetter << " donc recursivite gauche directe sur " << firstLetter << " !" << endl;
                return ri;
            } else {
                cout << " " << firstLetter << " = " << secondLetter << " donc recursivite gauche directe sur " << firstLetter << " !" << endl;
                return ri;
            }
        }

        // cas 2: on arrive sur un union (pipe | ), on change la deuxieme lettre � comparer (sL)
        else if (grammar->size() >= i + 1 && grammar->at(i) == "|") {
            cout << " On tombe sur un \"|\" donc sL = " << grammar->at(i + 1) << endl;
            secondLetter = grammar->at(i + 1);
        }

        // cas 3: on arrive sur un changement de regle (point-virgule ; ), donc on change les deux lettres � comparer (fL et sL)
        else if (grammar->size() >= i + 2 && grammar->at(i) == ";") {
            cout << " On tombe sur un \";\" donc fL = " << grammar->at(i + 1) << " et sL = " << grammar->at(i + 2) << endl;
            firstLetter = grammar->at(i + 1);
            secondLetter = grammar->at(i + 2);
            ri.ruleID++; // on incr�mente le num�ro de la r�gle
        }

        // cas 4: on n'a rep�r� aucun des cas pr�c�dents donc on avance d'un caract�re
        else
            cout << " On avance l'analyse d'un caractere..." << endl<< endl;
    }


    // fin si aucune r�cursivit� gauche directe detect�e avant
    cout << endl << endl << " - Fin de la grammaire -" << endl << endl;
    return ri0;
}



// fonction qui r�pare un cas de r�cursivit� gauche directe, renvoi si echec ou non
// grammar:vector<string> �tant la grammaire que l'on traite
// ri:RuleIdentificator �tant le param�tre de positionnement de la r�gle que l'on veut trait�e
bool repareDirectLeftRecursivity (vector<string> *grammar, RuleIdentificator ri) {
    vector<string> alpha, beta, rules, result_rules; // collection des alpha et des betas
    int firstPosition = -1, ruleID = 0;

    // on recherche la premi�re occurence de l'etat avec la r�cursivit�
    for (size_t i = 0; i < grammar->size(); i++) {
        if (grammar->at(i) == ";")
            ruleID++;
        if (grammar->at(i) == ri.ruleLetter && ruleID == ri.ruleID) { // on arrive sur l'etat presentant la recursivite gauche directe
            firstPosition = (int) i; // on ne prend que le regles de l'etat
            break;
        }
    }

    if (firstPosition >= 0) { // si on a trouv� l'etat, on va parcourir toutes ses regles

        bool loopAlpha = false;
        string currentAlpha, currentBeta;

        // on ne s�lectionne que les r�gle pour l'etat voulu
        for (size_t i = firstPosition; i < grammar->size(); i++) {
            if (grammar->at(i) == ";")
                break;
            else
                rules.push_back(grammar->at(i));
        }

        // si il n'y a pas de regle
        if (rules.empty())
            return false;

        // sinon, on boucle tant qu'il y a des etats
        for (size_t i = 0; i < rules.size(); i++) {

            currentAlpha = "";
            currentBeta = "";

            // si la lettre en cours est egale � l'etat, on a un alpha
            if (rules[i] == ri.ruleLetter) {
                loopAlpha = true; // on prendra le alpha au prochain tour
                continue;
            }

            // si on a pas de alpha alors on en d�duit qu'on a un beta
            else {
                if (!loopAlpha) {
                    while (i < rules.size()) {
                        if (rules[i] == "|")
                            break;
                        currentBeta += rules[i];
                        i++;
                    }
                    beta.push_back(currentBeta);
                }
            }

            // si on a l'ordre de selectionner un alpha,
            if (loopAlpha) {
                while (i < rules.size()) { // on parcourt le alpha de la regle
                    if (rules[i] == "|")
                        break;
                    currentAlpha += rules[i];
                    i++;
                }
                alpha.push_back(currentAlpha);
                loopAlpha = false;
            }
        }

        printVector(&alpha, "Ensemble des Alpha"); // on affiche les alpha
        printVector(&beta, "Ensemble des Beta"); // on affiche les beta

         // r�paration recursivit� directe
         // on genere le vecteur contenant les nouvelles regles
        string newNameState = ri.ruleLetter + "'";

        result_rules.push_back(ri.ruleLetter);
        for (size_t i = 0; i < beta.size(); i++) {
            result_rules.push_back(beta[i]);
            result_rules.push_back(newNameState);
            if (i + 1 < beta.size())
                result_rules.push_back("|");
        }
        result_rules.push_back(";");

        result_rules.push_back(newNameState);
        for (size_t i = 0; i < alpha.size(); i++) {
            result_rules.push_back(alpha[i]);
            result_rules.push_back(newNameState);
            if (i + 1 < alpha.size())
                result_rules.push_back("|");
        }
        result_rules.push_back("|");
        result_rules.push_back(epsilon);

        // on supprime les anciennes regles pour cette recursivit�
        // puis on insert les nouvelles � la place des anciennes
        grammar->erase(grammar->begin() + firstPosition, grammar->begin() + firstPosition+rules.size());
        grammar->insert(grammar->begin() + firstPosition, result_rules.begin(), result_rules.end());

        return true;
    }
    return false;
}





// fonction ne traitant qu'une seule r�gle r�cursive � gauche directement (renvoyant vrai ou faux selon son efficacit�)
// elle prend en param�tre la grammaire que l'on veut traiter
// et la r�gle d'identification correspondant au probl�me de r�cursivit� que l'on souhaite traiter
bool repareDirectLeftRecursivityFromLetter (vector<string> *grammar, RuleIdentificator ri) {

    if (getDirectLeftRecursivity(grammar, ri.ruleLetter).ruleID > -1) {
        repareDirectLeftRecursivity(grammar, ri);
        return true;
    }
    return false;
}




// fonction r�parant l'ensemble des r�cursivit�s gauche directe d'une grammaire (renvoit le nombre de r�gles trait�es (entre 0 et n))
// prend juste la grammaire en param�tre
unsigned repareAllDirectLeftRecursivity (vector<string> *grammar) {
    RuleIdentificator ri;
    unsigned counter = 0;

    ri = getDirectLeftRecursivity(grammar);
    if (ri.ruleID == -1)
        return 0;

    while (ri.ruleID > -1) {
        counter++;
        printNewTraitmentRule(ri.ruleLetter, ri.ruleID); // debug affichage
        repareDirectLeftRecursivity(grammar, ri); // r�pare la r�gle qui pose probleme (en fonction de la lettre + num�ro de regle)
        drawGrammar(grammar, "Grammaire traitee sur " + ri.ruleLetter); // debug affichage
        ri = getDirectLeftRecursivity(grammar); // donne la position de la regle posant � pr�sent probleme
    }

    cout << endl << " Nombre de regle(s) traitee(s) = " << counter << endl;
    return counter;
}



// proc�dure d'affichage pour debug et traces
void printNewTraitmentRule (string ruleLetter, int ruleID) {
    string letter = (ruleLetter == "") ? "aucune" : ruleLetter;

    cout << endl << endl << " ------- Nouvelle regle a traiter --------" << endl << endl;
    cout << " - Lettre de la regle = " << letter << endl;
    cout << " - ID de position = Regle #" << ruleID << endl << endl;
    cout << " -----------------------------------------" << endl << endl;
}







// routine main
int main()
{
    cout << endl << " � LANGAGE ET COMPILATION | TP 2" << endl << " � DESAMBIGUEUR LEXICAL C/C++" << endl;
    cout << " � ---------------------------------------------------------" << endl << " � CHRISTOPHE DE BATZ | L3  Groupe B" << endl;
    cout << " � ---------------------------------------------------------" << endl << " � Le \"epsilon\" est remplace par le \"diese\" #" << endl << endl;

    vector<string> *grammar = new vector<string>();
    readGrammarFile(grammar, "language3.txt");



    //printVector(grammar, "Grammaire AVANT");
    drawGrammar(grammar, "Grammaire de base");

    makeLeftFactorization(grammar);


    //repareAllDirectLeftRecursivity(grammar);

    //printVector(grammar, "Grammaire APRES");
    //drawGrammar(grammar, "Grammaire sans recursivite gauche directe");

    delete grammar;
    return EXIT_SUCCESS;
}
