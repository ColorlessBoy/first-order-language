from functools import wraps

def type_check(validType):
    def inner_type_check(func):
        @wraps(func)
        def head_check(*args):
            if args is not None:
                new_args = []
                for arg in args:
                    if isinstance(arg, validType):
                        new_args.append(arg)
                    else:
                        try:
                            arg = validType(arg)
                            new_args.append(arg)
                        except:
                            raise TypeError(f"Arguments are required to be {validType}.")
            return func(*new_args)
        return head_check

    def inner_type_check_list(func):
        @wraps(func)
        def head_check(*args):
            if args is None or len(args) != len(validType):
                raise ValueError(f"Require: len(args) == {len(validType)}")
            if args is not None:
                new_args = []
                for arg, t in zip(args, validType):
                    if isinstance(arg, t):
                        new_args.append(arg)
                    else:
                        try:
                            arg = t(arg)
                            new_args.append(arg)
                        except:
                            raise TypeError(f"{arg} are required to be {t}.")
            return func(*new_args)
        return head_check
    
    if isinstance(validType, list):
        return inner_type_check_list
    return inner_type_check
    