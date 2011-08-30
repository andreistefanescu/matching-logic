#!/usr/bin/env python3


import sys
import signal


###
class TimeoutException(Exception): 
    pass 


def timeout(timeout_time, timeout_handle):
    def timeout_function(function):
        def function_wrapper(*args):
            def raise_timeout(signum, frame):
                if signum == signal.SIGALRM:
                    raise TimeoutException()

            handler = signal.signal(signal.SIGALRM, raise_timeout) 
            signal.alarm(timeout_time)
            try: 
                return function(*args)
            except TimeoutException:
                return timeout_handle()
            finally:
                signal.alarm(0)
                signal.signal(signal.SIGALRM, handler) 
        return function_wrapper
    return timeout_function

