#pragma once

#include "NodeSet.h"

class DepthVisitor : public Visitor {
 private:
  // std::set<phoenix::Node*, NodeCompare> s;
  NodeSet s;

 public:

  DepthVisitor(phoenix::StoreNode *store) {
    store->accept(*this);
  }

  NodeSet getSet(void){
    return s;
  }

 private:

  void visit(phoenix::StoreNode *store) override {
    if (store->child->hasConstraint())
      store->child->accept(*this);
  }

  void visit(phoenix::UnaryNode *unary) override {
    if (!unary->hasConstraint())
      return;
    
    if (unary->child->hasConstraint()){
      unary->child->accept(*this);
    }
    else {
      s.insert(unary); // We already know at this point that unary has a constraint
    }
  }

  void visit(phoenix::CastNode *cast) override {
    cast->child->accept(*this);
  }

  void visit(phoenix::BinaryNode *binary) override {
    if (!binary->hasConstraint())
      return;
    
    if(!binary->left->hasConstraint() && !binary->right->hasConstraint()){
      s.insert(binary);
      return;
    }

    binary->left->accept(*this);
    binary->right->accept(*this);

  }

  void visit(phoenix::TargetOpNode *target) override {
    if (target->getOther()->hasConstraint()){
      target->getOther()->accept(*this);
    }
  }

  void visit(phoenix::TerminalNode *term) override {
    if (term->hasConstraint()){
      s.insert(term);
    }
  }
  
  void visit(phoenix::LoadNode *load) override {
    visit(cast<phoenix::TerminalNode>(load));
  }

  void visit(phoenix::ConstantNode *c) override {
    visit(cast<phoenix::TerminalNode>(c));
  }

  void visit(phoenix::ConstantIntNode *c) override {
    visit(cast<phoenix::TerminalNode>(c));
  }

  void visit(phoenix::ForeignNode *f) override {
    return;
  }
  
  void visit(phoenix::ArgumentNode *a) override {
    return;
  }

};