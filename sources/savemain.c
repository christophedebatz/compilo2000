#include <iostream>
#include <stdlib.h>
#include <vector>
#include <string.h>
#include <string>
#include <sstream>
#include <fstream>


// le "epsilon" est considéré ici comme un dièse (#), caractère réservé
#define epsilon "#"

using namespace std;


// structure permettant d'identifier précisement une règle
// int ruleID : numéro de la règle parmis les autres
// string ruleLetter : lettre correspondant à la règle
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





// imprime le contenu entier d'un vecteur (type utilisé ici : string)
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
// - chaque caractères est séparé d'un autre avec un espace blanc
// - pour une même règle concernant un seul non terminal, utilisez les pipes "|" pour les unions
// - séparer chaque règle concernant un non terminal différent du précédent par un point-virgule ";"
// - la fin de la grammaire se traduit par un aobase "@"
// - pour une meilleure lisibilité, sauter une ligne pour chaque nouvelle règle incluant un nouveau non terminal

void readGrammarFile(vector<string> *grammar, string fileName) {
    try {
        if ((unsigned)strlen(fileName.c_str()) <= 0)
        // si le nom contient au moins un caractère
            throw string("File " + fileName + " doesn't exist");

        // on créer le flux de lecture sur le fichier
        ifstream streamFile;
        streamFile.open(fileName.c_str());

        // on vérifie la bonne ouverture
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
// le motif doit toujours etre positionné en première position de chaque instruction pour etre comptabilisé
unsigned getNumberPatternRepetition (vector<string> pipedInstr, string pattern) {
    unsigned occCounter = 0; // compteur de motif

    // pour chaque instruction (union)...
    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        char *ptStr = strstr(pipedInstr[instr].c_str(), pattern.c_str()); // donne le pointeur sur la premiere occurence trouvée
        if (ptStr && *ptStr == pipedInstr[instr][0]) // si l'occurence trouvée est bien en première position de l'instruction alors OK
            occCounter++;
    }
    return occCounter;
}





// fonction renvoyant la liste de toutes les instructions factorisées (les betas) d'une regle
// parametres: le jeu d'instructions decoupé (vector), le motif qui factorise les instructions
vector<string> getFactorizableTerms (vector<string> pipedInstr, string pattern) {
    vector<string> factorizedTerms;

    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        if (pipedInstr[instr].substr(0, pattern.size()) == pattern) { // l'instruction actuelle contient le motif
            if (pipedInstr[instr].size() > pattern.size()) // l'instruction n'est pas terminée, on va donc factoriser le reste
                factorizedTerms.push_back(pipedInstr[instr].substr(pattern.size(), pipedInstr[instr].size() - 1));

            // sinon, l'instruction est terminé, on place epsilon
            else
                factorizedTerms.push_back(epsilon);
        }
    }

    return factorizedTerms;
}





// fonction donnant les instructions ne contenant pas le motif qu'on veut factoriser
// cette fonction prend un jeu d'instruction d'une regle en paramètre et le motif qu'on souhaite factoriser
// elle renvoi un vecteur contenant les instructions concernées
vector<string> getNonFactorizableTerms (vector<string> pipedInstr, string pattern) {
    vector<string> otherPatterns;

    for (size_t instr = 0; instr < pipedInstr.size(); instr++) {
        if (pipedInstr[instr].substr(0, pattern.size()) != pattern)
            otherPatterns.push_back(pipedInstr[instr]);
    }

    return otherPatterns;
}






// fonction donnant le motif le plus présent dans une expression de règle
// cette fonction prend en paramètre un vecteur contenant les instructions d'une regle
// en renvoi une chaine de caracteres representant le motif à factoriser
string getRuleLeftFactorizationPattern (vector<string> pipedInstr) {

    string currentPattern, globalPattern = "";
    unsigned currentNbRep = 0, globalNbRep = 0;

    // on cherche le plus grand motif commun à toutes les cases du vecteur des instructions
    for (size_t instr = 0; instr < pipedInstr.size(); instr++) { // on prend chaque instruction de la regle
        for (unsigned letter = 0; letter <= pipedInstr[instr].size(); letter++) { // pour chaque instruction on prend chaque caractere
            currentPattern = globalPattern + pipedInstr[instr][letter]; // on défini le nouveau motif
            currentNbRep = getNumberPatternRepetition(pipedInstr, currentPattern); // nombre de repetition pour ce nouveau motif..

            if (currentNbRep < globalNbRep) // si on est allé trop loin, on retourne le motif d'avant
                return globalPattern;

            globalNbRep = currentNbRep; // sinon on continu avec les valeurs actuelles
            globalPattern = currentPattern;
        } // endfor
    } // endfor

    return (globalNbRep <= 1) ? "" : globalPattern;
}




// fonction permettant de factoriser une grammaire à gauche
// fonction renvoyant vrai ou faux selon si elle a agit ou non
// elle prend une grammaire en paramètre
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

    for (size_t i = 0; i < grammar_copy.size(); i++) { // pour chaque règle, on applique
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
        else { // on arrive en bout de regle, on traite la regle avant de passer à la suivante

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

            for (unsigned p = 0; p < fPattern.size(); p++) { // on place le motif de factorisation à sa place
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




// parcourt la grammaire à la recherche de la première récursivité gauche directe trouvée
// le paramètre letter:string est facultatif et permet de ne detecter que les recursivité dûes à cette lettre
// fonction retournant la position exacte de la règle qui pose problème ainsi que la lettre représentant le non terminal recursif de la règle
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

    // on parcourt la grammaire car. par car. et on compare la première lettre (non terminal) aux premières lettre de chaque conditions
    for (size_t i = 2; i < grammar->size(); i++) {
        cout << endl << " i = " << i << endl;
        cout << " fL = " << firstLetter << " et sL = " << secondLetter << endl;
        ri.ruleLetter = firstLetter;

        // cas 1: on a equivalence des caractères donc récursivité gauche directe
        if (firstLetter == secondLetter) {
            if (letter != "" && firstLetter == letter) {
                cout << " " << firstLetter << " = " << secondLetter << " donc recursivite gauche directe sur " << firstLetter << " !" << endl;
                return ri;
            } else {
                cout << " " << firstLetter << " = " << secondLetter << " donc recursivite gauche directe sur " << firstLetter << " !" << endl;
                return ri;
            }
        }

        // cas 2: on arrive sur un union (pipe | ), on change la deuxieme lettre à comparer (sL)
        else if (grammar->size() >= i + 1 && grammar->at(i) == "|") {
            cout << " On tombe sur un \"|\" donc sL = " << grammar->at(i + 1) << endl;
            secondLetter = grammar->at(i + 1);
        }

        // cas 3: on arrive sur un changement de regle (point-virgule ; ), donc on change les deux lettres à comparer (fL et sL)
        else if (grammar->size() >= i + 2 && grammar->at(i) == ";") {
            cout << " On tombe sur un \";\" donc fL = " << grammar->at(i + 1) << " et sL = " << grammar->at(i + 2) << endl;
            firstLetter = grammar->at(i + 1);
            secondLetter = grammar->at(i + 2);
            ri.ruleID++; // on incrémente le numéro de la règle
        }

        // cas 4: on n'a repéré aucun des cas précédents donc on avance d'un caractère
        else
            cout << " On avance l'analyse d'un caractere..." << endl<< endl;
    }


    // fin si aucune récursivité gauche directe detectée avant
    cout << endl << endl << " - Fin de la grammaire -" << endl << endl;
    return ri0;
}



// fonction qui répare un cas de récursivité gauche directe, renvoi si echec ou non
// grammar:vector<string> étant la grammaire que l'on traite
// ri:RuleIdentificator étant le paramètre de positionnement de la règle que l'on veut traitée
bool repareDirectLeftRecursivity (vector<string> *grammar, RuleIdentificator ri) {
    vector<string> alpha, beta, rules, result_rules; // collection des alpha et des betas
    int firstPosition = -1, ruleID = 0;

    // on recherche la première occurence de l'etat avec la récursivité
    for (size_t i = 0; i < grammar->size(); i++) {
        if (grammar->at(i) == ";")
            ruleID++;
        if (grammar->at(i) == ri.ruleLetter && ruleID == ri.ruleID) { // on arrive sur l'etat presentant la recursivite gauche directe
            firstPosition = (int) i; // on ne prend que le regles de l'etat
            break;
        }
    }

    if (firstPosition >= 0) { // si on a trouvé l'etat, on va parcourir toutes ses regles

        bool loopAlpha = false;
        string currentAlpha, currentBeta;

        // on ne sélectionne que les règle pour l'etat voulu
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

            // si la lettre en cours est egale à l'etat, on a un alpha
            if (rules[i] == ri.ruleLetter) {
                loopAlpha = true; // on prendra le alpha au prochain tour
                continue;
            }

            // si on a pas de alpha alors on en déduit qu'on a un beta
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

         // réparation recursivité directe
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

        // on supprime les anciennes regles pour cette recursivité
        // puis on insert les nouvelles à la place des anciennes
        grammar->erase(grammar->begin() + firstPosition, grammar->begin() + firstPosition+rules.size());
        grammar->insert(grammar->begin() + firstPosition, result_rules.begin(), result_rules.end());

        return true;
    }
    return false;
}





// fonction ne traitant qu'une seule règle récursive à gauche directement (renvoyant vrai ou faux selon son efficacité)
// elle prend en paramètre la grammaire que l'on veut traiter
// et la règle d'identification correspondant au problème de récursivité que l'on souhaite traiter
bool repareDirectLeftRecursivityFromLetter (vector<string> *grammar, RuleIdentificator ri) {

    if (getDirectLeftRecursivity(grammar, ri.ruleLetter).ruleID > -1) {
        repareDirectLeftRecursivity(grammar, ri);
        return true;
    }
    return false;
}




// fonction réparant l'ensemble des récursivités gauche directe d'une grammaire (renvoit le nombre de règles traitées (entre 0 et n))
// prend juste la grammaire en paramètre
unsigned repareAllDirectLeftRecursivity (vector<string> *grammar) {
    RuleIdentificator ri;
    unsigned counter = 0;

    ri = getDirectLeftRecursivity(grammar);
    if (ri.ruleID == -1)
        return 0;

    while (ri.ruleID > -1) {
        counter++;
        printNewTraitmentRule(ri.ruleLetter, ri.ruleID); // debug affichage
        repareDirectLeftRecursivity(grammar, ri); // répare la règle qui pose probleme (en fonction de la lettre + numéro de regle)
        drawGrammar(grammar, "Grammaire traitee sur " + ri.ruleLetter); // debug affichage
        ri = getDirectLeftRecursivity(grammar); // donne la position de la regle posant à présent probleme
    }

    cout << endl << " Nombre de regle(s) traitee(s) = " << counter << endl;
    return counter;
}



// procédure d'affichage pour debug et traces
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
    cout << endl << " ² LANGAGE ET COMPILATION | TP 2" << endl << " ² DESAMBIGUEUR LEXICAL C/C++" << endl;
    cout << " ² ---------------------------------------------------------" << endl << " ² CHRISTOPHE DE BATZ | L3  Groupe B" << endl;
    cout << " ² ---------------------------------------------------------" << endl << " ² Le \"epsilon\" est remplace par le \"diese\" #" << endl << endl;

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
