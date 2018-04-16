{-@ reflect evalQUserEmail @-}
evalQUserEmail :: RefinedPersistFilter -> String -> String -> Bool
evalQUserEmail EQUAL filter given = given == filter
evalQUserEmail LE filter given = given <= filter
evalQUserEmail GE filter given = given >= filter
evalQUserEmail LTP filter given = given < filter
evalQUserEmail GTP filter given = given > filter
evalQUserEmail NE filter given = given /= filter

{-@ reflect evalQUserPassword @-}
evalQUserPassword :: RefinedPersistFilter -> Maybe String -> Maybe String -> Bool
evalQUserPassword EQUAL filter given = given == filter
evalQUserPassword NE filter given = given /= filter

{-@ reflect evalQUserVerkey @-}
evalQUserVerkey :: RefinedPersistFilter -> Maybe String -> Maybe String -> Bool
evalQUserVerkey EQUAL filter given = given == filter
evalQUserVerkey NE filter given = given /= filter

{-@ reflect evalQUserVerified @-}
evalQUserVerified :: RefinedPersistFilter -> Bool -> Bool -> Bool
evalQUserVerified EQUAL filter given = given == filter
evalQUserVerified NE filter given = given /= filter

{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserEmail -> evalQUserEmail (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail x)
    UserPassword -> evalQUserPassword (refinedFilterFilter filter) (refinedFilterValue filter) (userPassword x)
    UserVerkey -> evalQUserVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (userVerkey x)
    UserVerified -> evalQUserVerified (refinedFilterFilter filter) (refinedFilterValue filter) (userVerified x)
    UserId -> False

{-@ reflect evalQsUser @-}
evalQsUser :: [RefinedFilter User typ] -> User -> Bool
evalQsUser (f:fs) x = evalQUser f x && (evalQsUser fs x)
evalQsUser [] _ = True

{-@ assume selectUser :: f:[RefinedFilter User typ]
                -> [SelectOpt User]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:User | evalQsUser f v}] @-}
selectUser :: (PersistEntityBackend User ~ BaseBackend backend,
      PersistEntity User, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter User typ]
      -> [SelectOpt User]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity User]
selectUser fs ts = selectList (map toPersistentFilter fs) ts
{-@ reflect evalQEmailEmail @-}
evalQEmailEmail :: RefinedPersistFilter -> String -> String -> Bool
evalQEmailEmail EQUAL filter given = given == filter
evalQEmailEmail LE filter given = given <= filter
evalQEmailEmail GE filter given = given >= filter
evalQEmailEmail LTP filter given = given < filter
evalQEmailEmail GTP filter given = given > filter
evalQEmailEmail NE filter given = given /= filter

{-@ reflect evalQEmailUserId @-}
evalQEmailUserId :: RefinedPersistFilter -> Maybe UserId -> Maybe UserId -> Bool
evalQEmailUserId EQUAL filter given = given == filter
evalQEmailUserId NE filter given = given /= filter

{-@ reflect evalQEmailVerkey @-}
evalQEmailVerkey :: RefinedPersistFilter -> Maybe String -> Maybe String -> Bool
evalQEmailVerkey EQUAL filter given = given == filter
evalQEmailVerkey NE filter given = given /= filter

{-@ reflect evalQEmail @-}
evalQEmail :: RefinedFilter Email typ -> Email -> Bool
evalQEmail filter x = case refinedFilterField filter of
    EmailEmail -> evalQEmailEmail (refinedFilterFilter filter) (refinedFilterValue filter) (emailEmail x)
    EmailUserId -> evalQEmailUserId (refinedFilterFilter filter) (refinedFilterValue filter) (emailUserId x)
    EmailVerkey -> evalQEmailVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (emailVerkey x)
    EmailId -> False

{-@ reflect evalQsEmail @-}
evalQsEmail :: [RefinedFilter Email typ] -> Email -> Bool
evalQsEmail (f:fs) x = evalQEmail f x && (evalQsEmail fs x)
evalQsEmail [] _ = True

{-@ assume selectEmail :: f:[RefinedFilter Email typ]
                -> [SelectOpt Email]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:Email | evalQsEmail f v}] @-}
selectEmail :: (PersistEntityBackend Email ~ BaseBackend backend,
      PersistEntity Email, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Email typ]
      -> [SelectOpt Email]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity Email]
selectEmail fs ts = selectList (map toPersistentFilter fs) ts
{-@ reflect evalQPersonEmail @-}
evalQPersonEmail :: RefinedPersistFilter -> String -> String -> Bool
evalQPersonEmail EQUAL filter given = given == filter
evalQPersonEmail LE filter given = given <= filter
evalQPersonEmail GE filter given = given >= filter
evalQPersonEmail LTP filter given = given < filter
evalQPersonEmail GTP filter given = given > filter
evalQPersonEmail NE filter given = given /= filter

{-@ reflect evalQPersonName @-}
evalQPersonName :: RefinedPersistFilter -> String -> String -> Bool
evalQPersonName EQUAL filter given = given == filter
evalQPersonName LE filter given = given <= filter
evalQPersonName GE filter given = given >= filter
evalQPersonName LTP filter given = given < filter
evalQPersonName GTP filter given = given > filter
evalQPersonName NE filter given = given /= filter

{-@ reflect evalQPersonStreet @-}
evalQPersonStreet :: RefinedPersistFilter -> String -> String -> Bool
evalQPersonStreet EQUAL filter given = given == filter
evalQPersonStreet LE filter given = given <= filter
evalQPersonStreet GE filter given = given >= filter
evalQPersonStreet LTP filter given = given < filter
evalQPersonStreet GTP filter given = given > filter
evalQPersonStreet NE filter given = given /= filter

{-@ reflect evalQPersonNumber @-}
evalQPersonNumber :: RefinedPersistFilter -> Int -> Int -> Bool
evalQPersonNumber EQUAL filter given = given == filter
evalQPersonNumber LE filter given = given <= filter
evalQPersonNumber GE filter given = given >= filter
evalQPersonNumber LTP filter given = given < filter
evalQPersonNumber GTP filter given = given > filter
evalQPersonNumber NE filter given = given /= filter

{-@ reflect evalQPerson @-}
evalQPerson :: RefinedFilter Person typ -> Person -> Bool
evalQPerson filter x = case refinedFilterField filter of
    PersonEmail -> evalQPersonEmail (refinedFilterFilter filter) (refinedFilterValue filter) (personEmail x)
    PersonName -> evalQPersonName (refinedFilterFilter filter) (refinedFilterValue filter) (personName x)
    PersonStreet -> evalQPersonStreet (refinedFilterFilter filter) (refinedFilterValue filter) (personStreet x)
    PersonNumber -> evalQPersonNumber (refinedFilterFilter filter) (refinedFilterValue filter) (personNumber x)
    PersonId -> False

{-@ reflect evalQsPerson @-}
evalQsPerson :: [RefinedFilter Person typ] -> Person -> Bool
evalQsPerson (f:fs) x = evalQPerson f x && (evalQsPerson fs x)
evalQsPerson [] _ = True

{-@ assume selectPerson :: f:[RefinedFilter Person typ]
                -> [SelectOpt Person]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:Person | evalQsPerson f v}] @-}
selectPerson :: (PersistEntityBackend Person ~ BaseBackend backend,
      PersistEntity Person, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Person typ]
      -> [SelectOpt Person]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity Person]
selectPerson fs ts = selectList (map toPersistentFilter fs) ts
{-@ reflect evalQFriendsEmail @-}
evalQFriendsEmail :: RefinedPersistFilter -> String -> String -> Bool
evalQFriendsEmail EQUAL filter given = given == filter
evalQFriendsEmail LE filter given = given <= filter
evalQFriendsEmail GE filter given = given >= filter
evalQFriendsEmail LTP filter given = given < filter
evalQFriendsEmail GTP filter given = given > filter
evalQFriendsEmail NE filter given = given /= filter

{-@ reflect evalQFriendsRequests @-}
evalQFriendsRequests :: RefinedPersistFilter -> [String] -> [String] -> Bool
evalQFriendsRequests EQUAL filter given = given == filter
evalQFriendsRequests LE filter given = given <= filter
evalQFriendsRequests GE filter given = given >= filter
evalQFriendsRequests LTP filter given = given < filter
evalQFriendsRequests GTP filter given = given > filter
evalQFriendsRequests NE filter given = given /= filter

{-@ reflect evalQFriendsFriends @-}
evalQFriendsFriends :: RefinedPersistFilter -> [String] -> [String] -> Bool
evalQFriendsFriends EQUAL filter given = given == filter
evalQFriendsFriends LE filter given = given <= filter
evalQFriendsFriends GE filter given = given >= filter
evalQFriendsFriends LTP filter given = given < filter
evalQFriendsFriends GTP filter given = given > filter
evalQFriendsFriends NE filter given = given /= filter

{-@ reflect evalQFriendsOutgoingRequests @-}
evalQFriendsOutgoingRequests :: RefinedPersistFilter -> [String] -> [String] -> Bool
evalQFriendsOutgoingRequests EQUAL filter given = given == filter
evalQFriendsOutgoingRequests LE filter given = given <= filter
evalQFriendsOutgoingRequests GE filter given = given >= filter
evalQFriendsOutgoingRequests LTP filter given = given < filter
evalQFriendsOutgoingRequests GTP filter given = given > filter
evalQFriendsOutgoingRequests NE filter given = given /= filter

{-@ reflect evalQFriends @-}
evalQFriends :: RefinedFilter Friends typ -> Friends -> Bool
evalQFriends filter x = case refinedFilterField filter of
    FriendsEmail -> evalQFriendsEmail (refinedFilterFilter filter) (refinedFilterValue filter) (friendsEmail x)
    FriendsRequests -> evalQFriendsRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsRequests x)
    FriendsFriends -> evalQFriendsFriends (refinedFilterFilter filter) (refinedFilterValue filter) (friendsFriends x)
    FriendsOutgoingRequests -> evalQFriendsOutgoingRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsOutgoingRequests x)
    FriendsId -> False

{-@ reflect evalQsFriends @-}
evalQsFriends :: [RefinedFilter Friends typ] -> Friends -> Bool
evalQsFriends (f:fs) x = evalQFriends f x && (evalQsFriends fs x)
evalQsFriends [] _ = True

{-@ assume selectFriends :: f:[RefinedFilter Friends typ]
                -> [SelectOpt Friends]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:Friends | evalQsFriends f v}] @-}
selectFriends :: (PersistEntityBackend Friends ~ BaseBackend backend,
      PersistEntity Friends, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Friends typ]
      -> [SelectOpt Friends]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity Friends]
selectFriends fs ts = selectList (map toPersistentFilter fs) ts
