#ifndef __MPP__
#define __MPP__

#include <iostream>
#include <string>
#include <cassert>
#include <cstdarg>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <initializer_list>
#include <atomic>
#include <tuple>
using namespace std;

enum {
    LOGICAL,
    QUANTIFIER,
    PROPERTY,
    FUNCTION,
    VARIABLE,
    ASSUME,
    LET,
    PROOF,
    TYPE_BOUND
};

enum {
    NOT,
    AND,
    OR,
    IMPLY,
    IFF,
    LOGICAL_SUBTYPE_BOUND
};

enum {
    ALL,
    EXIST,
    UNIQUE,
    UNIQUELY_EXIST,
    QUNATIFIER_SUBTYPE_BOUND
};

enum {
    EQUAL,
    IN,
    INCLUSION,
    PROPER_INCLUSION,
    UNARY_CUP,
    UNARY_CAP,
    BINARY_CUP,
    BINARY_CAP,
    EVALUATION,
    ELEMENTARY_SUBTYPE_BOUND
};



class Node{
    private:
        inline static thread_local int ID_counter;
        inline static thread_local int thread;
        inline static thread_local set<Node*> garbages;

        static map<string, set<Node*>> global_theorems;
        inline static thread_local stack<map<string, set<Node*>>> local_theorems;

        static atomic<int> subtype_counter;
        static int get_new_subtype(){
            return atomic_fetch_add(&subtype_counter, 1);
        }

        int type;
        int arity;
        int subtype;
        vector<Node*> children;

        bool _variable;
        bool _term;
        bool _sentence;

        set<int> free;
        set<int> bounded;

    public:
        // initializers
        static void set_thread(int number){
            thread = number;
        }

        Node(
            int _type,
            int _subtype,
            vector<Node*> _children
        ):
        arity(_children.size()),
        children(_children)
        {
            type = _type;
            int bound_subtype;

            switch(_type){
                case LOGICAL:
                    for(Node* child: _children) assert(child->is_sentence());
                    assert(_subtype < LOGICAL_SUBTYPE_BOUND);

                    if(_subtype == NOT) assert(arity == 1);
                    else assert(arity == 2);
                    
                    subtype = _subtype;
                    _sentence = true;

                    free = children[0]->get_free();
                    bounded = children[0]->get_bounded();

                    if(_type != NOT){
                        for(int free_subtype : children[1]->get_free()){
                            assert(bounded.find(free_subtype) == bounded.end()); // readiblity
                            free.insert(free_subtype);
                        }
                        for(int bounded_subtype : children[1]->get_bounded()){
                            assert(bounded.find(bounded_subtype) == bounded.end()); // readability
                            bounded.insert(bounded_subtype);
                        }
                    }
                    break;
                case QUANTIFIER:
                    assert(arity == 2);
                    assert(children[0]->is_variable());
                    assert(children[1]->is_sentence());
                    assert(_subtype < QUNATIFIER_SUBTYPE_BOUND);
                    subtype = _subtype;
                    _sentence = true;

                    bound_subtype = children[0]->get_subtype();
                    for(int free_subtype : children[1]->get_free()){
                        if(free_subtype != bound_subtype) free.insert(free_subtype);
                    }
                    bounded.insert(bound_subtype);
                    for(int bounded_subtype : children[1]->get_bounded()){
                        if(bound_subtype == bounded_subtype) assert(false); // readability
                        bounded.insert(bounded_subtype);
                    }
                    break;
                case PROPERTY:
                    for(Node* child : _children){
                        assert(child->is_term());
                        for(int free_subtype : child->get_free()) free.insert(free_subtype); 
                    }
                    subtype = _subtype;
                    _sentence = true;
                    break;
                case FUNCTION:
                    for(Node* child : _children){
                        assert(child->is_term());
                        for(int free_subtype : child->get_free()) free.insert(free_subtype); 
                    }
                    subtype = _subtype;
                    _term = true;
                    break;
                case VARIABLE:
                    assert(ID_counter < ~0x0u);
                    assert(arity == 0);
                    subtype = ID_counter++;
                    free.insert(subtype);
                    _term = true;
                    _variable = true;
                    break;
                case ASSUME:
                    assert(arity >= 1);
                    assert(children[0]->is_sentence());
                    for(int index = 1; index < arity; index++) assert(children[index]->is_block_or_sentence());
                    break;
                case LET:
                    assert(arity >= 2);
                    assert(children[0]->is_variable());
                    assert(children[1]->is_sentence());
                    for(int index = 2; index < arity; index++) assert(children[index]->is_block_or_sentence());
                    break;
                case PROOF:
                    for(Node* child : _children) assert(child->is_block_or_sentence());
                    local_theorems.push(map<string, set<Node*>>());
                    break;
                default:
                    assert(false);
            }

            garbages.insert(this);
        }


        // string generation
        string term_to_string(){
            assert(is_term());
            if(is_variable()){
                return "v" + to_string(subtype);
            } else {
                string answer = "f" + to_string(subtype) + "(";
                for(Node* child : children) answer += (child->term_to_string() + ",");
                return answer;
            }
        }

        set<tuple<string,int,map<int,int>,map<string,set<int>>>> __get_hooks(
            set<tuple<string,int,map<int,int>,map<string,set<int>>>> history){

            string prefix;
            int numbering;
            map<int,int> fixed_mapping;
            map<string,set<int>> flexible_mapping;
            set<tuple<string,int,map<int,int>,map<string,set<int>>>> history_temporary;

            if(is_sentence()){
                for(tuple<string,int,map<int,int>,map<string,set<int>>> branch : history){
                    prefix = get<0>(branch);
                    numbering = get<1>(branch);
                    fixed_mapping = get<2>(branch);
                    flexible_mapping = get<3>(branch);

                    if(type == LOGICAL) prefix += ("L" + to_string(subtype) + "(" + (arity? "": ")"));
                    else if(type == QUANTIFIER){
                        prefix += ("Q" + to_string(subtype) + "/" + to_string(numbering) + "(" + (arity? "": ")"));
                        fixed_mapping.insert_or_assign(subtype, numbering);
                        numbering++;
                    } else if(type == PROPERTY) prefix += ("P" + to_string(subtype) + "(" + (arity? "": ")"));
                    else assert(false);
                    history_temporary.insert({prefix, numbering, fixed_mapping, flexible_mapping});
                }
                history = history_temporary;
                history_temporary = set<tuple<string,int,map<int,int>,map<string,set<int>>>>();

                for(int index = 0; index < arity; index++){
                    for(tuple<string,int,map<int,int>,map<string,set<int>>> branch : children[index]->__get_hooks(history)){
                        prefix = get<0>(branch);
                        numbering = get<1>(branch);
                        fixed_mapping = get<2>(branch);
                        flexible_mapping = get<3>(branch);

                        prefix += ",";
                        if (index == arity - 1) prefix += ")";
                        history_temporary.insert({prefix, numbering, fixed_mapping, flexible_mapping});
                    }
                    history = history_temporary;
                    history_temporary = set<tuple<string,int,map<int,int>,map<string,set<int>>>>();
                }
            } else if(is_term()){
                string current_term_string = term_to_string();

                for(tuple<string,int,map<int,int>,map<string,set<int>>> branch : history){
                    prefix = get<0>(branch);
                    numbering = get<1>(branch);
                    fixed_mapping = get<2>(branch);
                    flexible_mapping = get<3>(branch);

                    if(is_variable()){
                        map<int,int>::iterator fixed = fixed_mapping.find(subtype);
                        if(fixed != fixed_mapping.end()) {
                            prefix += ("V" + to_string(subtype));
                            history_temporary.insert({prefix, numbering, fixed_mapping, flexible_mapping});
                        } else {
                            map<string,set<int>>::iterator flexible = flexible_mapping.find(current_term_string);
                            if(flexible != flexible_mapping.end()){
                                for(int mark : flexible->second){
                                    history_temporary.insert({prefix + "V" + to_string(mark), numbering, fixed_mapping, flexible_mapping});
                                }
                            }
                            flexible_mapping.insert_or_assign(current_term_string, set<int>({numbering}));
                            history_temporary.insert({prefix + "V" + to_string(numbering), numbering + 1, fixed_mapping, flexible_mapping});
                        }
                        history = history_temporary;
                    } else if(is_term()){
                        bool is_free = true;
                        for(int free_subtype : free){
                            if(fixed_mapping.find(free_subtype) != fixed_mapping.end()){
                                is_free = false;
                                break;
                            }
                        }
                        map<string,set<int>>::iterator flexible = flexible_mapping.find(current_term_string);
                        if(flexible != flexible_mapping.end()){
                            for(int mark : flexible->second){
                                history_temporary.insert({prefix + "F" + to_string(mark) + "(" + (arity? "" : ")"), numbering, fixed_mapping, flexible_mapping});
                            }
                        }
                        if(is_free){
                            flexible_mapping.insert_or_assign(current_term_string, set<int>({numbering}));
                            history_temporary.insert({prefix + "F" + to_string(numbering) + "(" + (arity? "" : ")"), numbering + 1, fixed_mapping, flexible_mapping});
                        }
                        history = history_temporary;
                        history_temporary = set<tuple<string,int,map<int,int>,map<string,set<int>>>>();
                        for(int index = 0; index < arity; index++){
                            for(tuple<string,int,map<int,int>,map<string,set<int>>> branch : children[index]->__get_hooks(history)){
                                prefix = get<0>(branch);
                                numbering = get<1>(branch);
                                fixed_mapping = get<2>(branch);
                                flexible_mapping = get<3>(branch);

                                prefix += ",";
                                if (index == arity - 1) prefix += ")";
                                history_temporary.insert({prefix, numbering, fixed_mapping, flexible_mapping});
                            }
                            history = history_temporary;
                            history_temporary = set<tuple<string,int,map<int,int>,map<string,set<int>>>>();
                        }
                    } else assert(false);
                }
            } else assert(false);

            return history;
        }

        set<string> get_hooks(){
            set<tuple<string,int,map<int,int>,map<string,set<int>>>> results = __get_hooks(set<tuple<string,int,map<int,int>,map<string,set<int>>>>());
            set<string> answer;
            for(tuple<string,int,map<int,int>,map<string,set<int>>> result : results){
                answer.insert(get<0>(result));
            }
            return answer;
        }



        // at the end
        static void collect(){
            for(Node* garbage : garbages) delete garbage;
        }


        // getters
        bool is_variable(){
            return _variable;
        }

        bool is_term(){
            return _term;
        }

        bool is_sentence(){
            return _sentence;
        }

        bool is_quantifier(){
            return (type == QUANTIFIER);
        }

        bool is_block_or_sentence(){
            return is_sentence() || type == ASSUME || type == LET;
        }

        bool is_closed(){
            return is_sentence() && !free.size();
        }

        int get_type(){
            return type;
        }

        int get_subtype(){
            return subtype;
        }

        int get_arity(){
            return arity;
        }

        Node* left(){
            assert(type == LOGICAL && subtype != NOT);
            return children[0];
        }

        Node* right(){
            assert(type == LOGICAL && subtype != NOT);
            return children[1];
        }

        Node* bound(){
            assert(type == QUANTIFIER);
            return children[0];
        }

        Node* body(){
            assert(type == QUANTIFIER || (type == LOGICAL && subtype == NOT));
            return children[1];
        }

        Node* assumption(){
            if(type == ASSUME) return children[0];
            else if(type == LET) return children[1];
            else assert(false);
        }

        Node* variable(){
            if(type == LET) return children[0];
            else assert(false);
        }

        set<int> get_free(){
            return free;
        }

        set<int> get_bounded(){
            return bounded;
        }


        // overloaders
        Node& operator~(){
            return *(new Node(LOGICAL, NOT, {this}));
        }

        Node& operator&&(Node& A){
            return *(new Node(LOGICAL, AND, {this, &A}));
        }

        Node& operator||(Node& A){
            return *(new Node(LOGICAL, OR, {this, &A}));
        }

        Node& operator>>(Node& A){
            return *(new Node(LOGICAL, IMPLY, {this, &A}));
        }

        Node& operator==(Node& A){
            if(is_sentence()) return *(new Node(LOGICAL, IFF, {this, &A}));
            else if (is_term()) return *(new Node(FUNCTION, EQUAL, {this, &A}));
            else {
                assert(false);
                return *(Node*)NULL;
            }
        }

        Node& operator!=(Node& A){
            return ~(*this == A);
        }

        Node& operator%(Node& A){
            return *(new Node(PROPERTY, IN, {this, &A}));
        }

        Node& operator<<=(Node& A){
            return *(new Node(PROPERTY, INCLUSION, {this, &A}));
        }

        Node& operator<<(Node& A){
            return *(new Node(PROPERTY, PROPER_INCLUSION, {this, &A}));
        }

        Node& operator++(){
            return *(new Node(FUNCTION, UNARY_CUP, {this}));
        }

        Node& operator--(){
            return *(new Node(FUNCTION, UNARY_CAP, {this}));
        }

        Node& operator|(Node& A){
            return *(new Node(FUNCTION, BINARY_CUP, {this, &A}));
        }

        Node& operator&(Node& A){
            return *(new Node(FUNCTION, BINARY_CAP, {this, &A}));
        }

        Node& operator[](int index){
            return *children[index];
        }

        Node& operator()(initializer_list<Node> arguments){
            vector<Node*> _children;
            for(Node argument : arguments) _children.push_back(&argument);
            if(type == PROPERTY || type == FUNCTION){
                return *(new Node(FUNCTION, subtype, _children));
            } else if(type == VARIABLE){
                return *(new Node(FUNCTION, EVALUATION, _children));
            }
        }

        void preserve(){
            garbages.erase(this);
            for(Node* child : children) child->preserve();
        }

};


using var = Node&;

Node& Var(){
    return *(new Node(VARIABLE, 0, {}));
}

Node& assume(Node& assumption, initializer_list<Node> sentences){
    vector<Node*> push_forward;
    push_forward.push_back(&assumption);
    for(Node sentence : sentences) push_forward.push_back(&sentence);
    return *(new Node(ASSUME, 0, push_forward));
}

Node& let(Node& variable, Node& assumption, initializer_list<Node> sentences){
    vector<Node*> push_forward;
    push_forward.push_back(&variable);
    push_forward.push_back(&assumption);
    for(Node sentence : sentences) push_forward.push_back(&sentence);
    return *(new Node(ASSUME, 0, push_forward));
}

Node& proof(initializer_list<Node> sentences){
    vector<Node*> push_forward;
    for(Node sentence : sentences) push_forward.push_back(&sentence);
    return *(new Node(PROOF, 0, push_forward));
}



#endif