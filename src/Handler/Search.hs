{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Search where

import Import

searchForm :: Html -> MForm Handler (FormResult Text, Widget)
searchForm = renderDivs $ areq textField "Search" Nothing

getSearchResults :: String -> Handler [Documents]
getSearchResults s = do
  myEmail <- getAuthEmail
  ret <- case myEmail of
           Nothing -> return []
           Just me -> runDB $ do
             docs <- selectList [DocumentsType ==. s] []
             consents <- mapM (\(Entity _ (Documents _ _ consent _)) -> selectList [ConsentConsentID ==. consent,
                                                                                    ConsentPermittedUser ==. me] [])
                         docs
             validDocs <- return $ let flatConsents = concat consents in
                                     map (\(x, Entity _ doc) -> doc) $ filter (not . null . fst) $ zip consents docs
             return $ (validDocs :: [Documents])
  return ret


postSearchR :: Handler Html
postSearchR = do
  ((result, widget), enctype) <- runFormPost searchForm
  case result of
    FormSuccess s -> do
      {- _ <- runDB $ do
         _ <- insert (Documents ("1234" :: String) ("PsTNote" :: String) 1234 ("FooBar" :: String))
         insert (Consent 1234 "jluningp@andrew.cmu.edu" "hmm") -}
      results <- getSearchResults (unpack s)
      defaultLayout $(widgetFile "searchPost")
    {-
     - Filter based on whether the keyword is in the title
     - Only show results that the particular user has an authorization for in the
       authorization table
     -}
    _ -> defaultLayout $(widgetFile "searchPostFail")

getSearchR :: Handler Html
getSearchR = do
  (widget, enctype) <- generateFormPost searchForm
  defaultLayout $(widgetFile "search")


getAuthEmail :: Handler (Maybe String)
getAuthEmail = do
    myId <- maybeAuthId
    case myId of
      Nothing -> return $ Nothing
      Just id -> runDB $ do
        user <- get id
        return $ case user of
                   Nothing -> Nothing
                   Just (User email _ _ _) -> Just email
