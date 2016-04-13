'''
CC BY-SA 3.0
Creative Commons Attribution-ShareAlike 3.0 Unported
http://creativecommons.org/licenses/by-sa/3.0/
Sourced from:
http://code.activestate.com/recipes/66531-singleton-we-dont-need-no-stinkin-singleton-the-borg/
'''
#An alternative to singletons. All instances of a particular subclass of Borg will have the exact same state
class Borg:
    _shared_state = {}
    def __init__(self):
        self.__dict__ = self._shared_state
