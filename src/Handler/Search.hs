{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Search where

import Import

getSearchR :: Handler Html
getSearchR = do
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
