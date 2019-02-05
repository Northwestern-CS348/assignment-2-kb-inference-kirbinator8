import read
import copy
from util import *
from logical_classes import *

verbose = 0


class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])

        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def help(self, fact_or_rule):
        if (factq(fact_or_rule)) and (fact_or_rule in self.facts):
            fact = self._get_fact(fact_or_rule)
            supporting_facts = fact.supports_facts
            supporting_rules = fact.supports_rules

            if (fact.supported_by):
                fact.asserted = False
            else:
                for j in supporting_facts:
                    supportingf = self._get_fact(j)

                    for k in supportingf.supported_by:
                        if k[0] == fact:
                            supportingf.supported_by.remove(k)

                    self.help(supportingf)

                for j in supporting_rules:
                    supportingr = self._get_rule(j)
                    for k in supportingr.supported_by:
                        if k[0] == fact:
                            supportingr.supported_by.remove(k)
                    self.help(supportingr)
                self.facts.remove(fact)

        elif fact_or_rule in self.rules:
            rule = self._get_rule(fact_or_rule)
            supporting_facts1 = rule.supports_facts
            supporting_rules1 = rule.supports_rules
            if (len(rule.supported_by) < 1) and (not (rule.asserted)):
                for j in supporting_facts1:
                    supportingf = self._get_fact(j)
                    for k in supportingf.supported_by:
                        if k[1] == rule:
                            supportingf.supported_by.remove(k)

                    self.help(supportingf)

                for j in supporting_rules1:
                    supportingr = self._get_rule(j)
                    for k in supportingr.supported_by:
                        if k[1] == rule:
                            supportingr.supported_by.remove(k)
                    self.help(supportingr)
                self.rules.remove(rule)

    def kb_retract(self, fact):
        """Retract a fact from the KB
        Args:
            fact (Fact) - Fact to be retracted
        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here
        if factq(fact):
            self.help(fact)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
               [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        my_binding = match(fact.statement, rule.lhs[0])
        my_pair = [fact, rule]

        if (my_binding != False):

            if (len(rule.lhs) == 1):
                my_fact = Fact(instantiate(rule.rhs, my_binding))

                rule.supports_facts.append(my_fact)
                fact.supports_facts.append(my_fact)

                my_fact.supported_by.append(my_pair)
                kb.kb_assert(my_fact)

            elif (len(rule.lhs) > 1):
                left = []
                for i in range(len(rule.lhs) - 1):
                    left.append(instantiate(rule.lhs[i + 1], my_binding))

                left = [left, instantiate(rule.rhs, my_binding)]
                my_rule = Rule(left)

                rule.supports_rules.append(my_rule)
                fact.supports_rules.append(my_rule)

                my_rule.supported_by.append(my_pair)
                kb.kb_assert(my_rule)
